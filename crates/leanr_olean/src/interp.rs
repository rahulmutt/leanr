//! Phase B: interpret the validated [`RawValue`] DAG into
//! `leanr_kernel` types, following the layout table in the M1a plan
//! (each conversion cites its oracle definition). Phase A already
//! bounds-checked every byte, so this module only checks *shape*.
//!
//! Sharing: per-type memos keyed by raw node address map one file
//! offset to one `Arc`, preserving the file's DAG structure (the
//! oracle max-shares aggressively; naive tree conversion would explode
//! memory). Expr/Level conversion is an explicit-stack post-order walk
//! because term depth is attacker-controlled.

use std::collections::HashMap;
use std::sync::Arc;

use leanr_kernel::{
    AxiomVal, BinderInfo, ConstantInfo, ConstantVal, ConstructorVal, DataValue, DefinitionSafety,
    DefinitionVal, Expr, InductiveVal, Int, KVMap, Level, Literal, Name, Nat, OpaqueVal, QuotKind,
    QuotVal, RecursorRule, RecursorVal, ReducibilityHints, TheoremVal,
};
use num_bigint::{BigInt, BigUint};

use crate::raw::RawValue;
use crate::OleanError;

type Raw = Arc<RawValue>;

fn key(r: &Raw) -> *const RawValue {
    Arc::as_ptr(r)
}

fn bad(expected: &'static str) -> OleanError {
    OleanError::BadShape { expected }
}

/// Exact-count ctor accessor: `m_other` is the writer's exact pointer
/// field count, so field counts are exact; scalar areas may be padded
/// (layout reference), so those are minimum checks at use sites.
fn ctor<'r>(
    r: &'r Raw,
    tag: u8,
    fields: usize,
    expected: &'static str,
) -> Result<(&'r [Raw], &'r [u8]), OleanError> {
    match &**r {
        RawValue::Ctor {
            tag: t,
            fields: f,
            scalars,
        } if *t == tag && f.len() == fields => Ok((f, scalars)),
        _ => Err(bad(expected)),
    }
}

fn boolean(byte: Option<&u8>, expected: &'static str) -> Result<bool, OleanError> {
    match byte.copied() {
        Some(0) => Ok(false),
        Some(1) => Ok(true),
        _ => Err(bad(expected)),
    }
}

fn nat(r: &Raw) -> Result<Nat, OleanError> {
    match &**r {
        RawValue::Scalar(v) => Ok(Nat::from(*v)),
        RawValue::BigInt(i) => {
            let mag: BigUint = i.clone().try_into().map_err(|_| bad("non-negative Nat"))?;
            Ok(Nat(mag))
        }
        _ => Err(bad("Nat")),
    }
}

fn int(r: &Raw) -> Result<Int, OleanError> {
    match &**r {
        // Boxed Int scalars are 63-bit two's complement (lean.h
        // lean_scalar_to_int): sign-extend from bit 62.
        RawValue::Scalar(v) => Ok(Int(BigInt::from(((v << 1) as i64) >> 1))),
        RawValue::BigInt(i) => Ok(Int(i.clone())),
        _ => Err(bad("Int")),
    }
}

fn string(r: &Raw) -> Result<String, OleanError> {
    match &**r {
        RawValue::Str(s) => Ok(s.clone()),
        _ => Err(bad("String")),
    }
}

/// `List α` → element raw nodes (nil = box(0), cons = tag 1).
fn list(r: &Raw) -> Result<Vec<&Raw>, OleanError> {
    let mut items = Vec::new();
    let mut cur = r;
    loop {
        match &**cur {
            RawValue::Scalar(0) => return Ok(items),
            RawValue::Ctor { tag: 1, fields, .. } if fields.len() == 2 => {
                items.push(&fields[0]);
                cur = &fields[1];
            }
            _ => return Err(bad("List")),
        }
    }
}

fn array(r: &Raw) -> Result<&[Raw], OleanError> {
    match &**r {
        RawValue::Array(elems) => Ok(elems),
        _ => Err(bad("Array")),
    }
}

pub(crate) struct Interp {
    names: HashMap<*const RawValue, Arc<Name>>,
    levels: HashMap<*const RawValue, Arc<Level>>,
    exprs: HashMap<*const RawValue, Arc<Expr>>,
    anonymous: Arc<Name>,
    zero: Arc<Level>,
}

impl Interp {
    pub(crate) fn new() -> Interp {
        Interp {
            names: HashMap::new(),
            levels: HashMap::new(),
            exprs: HashMap::new(),
            anonymous: Arc::new(Name::Anonymous),
            zero: Arc::new(Level::Zero),
        }
    }

    /// Name (Init/Prelude.lean:4693-4717): walk the parent chain down
    /// iteratively, then build back up, memoizing each node.
    fn name(&mut self, r: &Raw) -> Result<Arc<Name>, OleanError> {
        let mut chain: Vec<&Raw> = Vec::new();
        let mut cur = r;
        let mut built = loop {
            if let RawValue::Scalar(0) = &**cur {
                break Arc::clone(&self.anonymous);
            }
            if let Some(n) = self.names.get(&key(cur)) {
                break Arc::clone(n);
            }
            match &**cur {
                RawValue::Ctor {
                    tag: 1 | 2, fields, ..
                } if fields.len() == 2 => {
                    chain.push(cur);
                    cur = &fields[0];
                }
                _ => return Err(bad("Name")),
            }
        };
        for node in chain.into_iter().rev() {
            let RawValue::Ctor { tag, fields, .. } = &**node else {
                unreachable!()
            };
            let name = match tag {
                1 => Name::Str {
                    parent: built,
                    part: string(&fields[1])?,
                },
                2 => Name::Num {
                    parent: built,
                    part: nat(&fields[1])?,
                },
                _ => unreachable!(),
            };
            built = Arc::new(name);
            self.names.insert(key(node), Arc::clone(&built));
        }
        Ok(built)
    }

    fn sub_level(&self, r: &Raw) -> Result<Arc<Level>, OleanError> {
        if let RawValue::Scalar(0) = &**r {
            return Ok(Arc::clone(&self.zero));
        }
        self.levels
            .get(&key(r))
            .cloned()
            .ok_or_else(|| bad("Level subterm"))
    }

    /// Level (Level.lean:90-103): explicit-stack post-order.
    fn level(&mut self, root: &Raw) -> Result<Arc<Level>, OleanError> {
        enum Step<'r> {
            Visit(&'r Raw),
            Build(&'r Raw),
        }
        let mut stack = vec![Step::Visit(root)];
        while let Some(step) = stack.pop() {
            match step {
                Step::Visit(r) => {
                    if matches!(&**r, RawValue::Scalar(0)) || self.levels.contains_key(&key(r)) {
                        continue;
                    }
                    let RawValue::Ctor { tag, fields, .. } = &**r else {
                        return Err(bad("Level"));
                    };
                    let n_level_children = match tag {
                        1 => 1,     // succ
                        2 | 3 => 2, // max, imax
                        4 | 5 => 0, // param, mvar (Name field)
                        _ => return Err(bad("Level tag")),
                    };
                    let expected_fields = if *tag == 1 {
                        1
                    } else if *tag <= 3 {
                        2
                    } else {
                        1
                    };
                    if fields.len() != expected_fields {
                        return Err(bad("Level fields"));
                    }
                    stack.push(Step::Build(r));
                    for f in &fields[..n_level_children] {
                        stack.push(Step::Visit(f));
                    }
                }
                Step::Build(r) => {
                    let RawValue::Ctor { tag, fields, .. } = &**r else {
                        unreachable!()
                    };
                    let level = match tag {
                        1 => Level::Succ(self.sub_level(&fields[0])?),
                        2 => Level::Max(self.sub_level(&fields[0])?, self.sub_level(&fields[1])?),
                        3 => Level::IMax(self.sub_level(&fields[0])?, self.sub_level(&fields[1])?),
                        4 => Level::Param(self.name(&fields[0])?),
                        5 => Level::MVar(self.name(&fields[0])?),
                        _ => unreachable!(),
                    };
                    self.levels.insert(key(r), Arc::new(level));
                }
            }
        }
        self.sub_level(root)
    }

    fn sub_expr(&self, r: &Raw) -> Result<Arc<Expr>, OleanError> {
        self.exprs
            .get(&key(r))
            .cloned()
            .ok_or_else(|| bad("Expr subterm"))
    }

    /// Expr (Expr.lean:321-471): explicit-stack post-order over the
    /// Expr-typed fields; Name/Level/Literal fields convert inline.
    fn expr(&mut self, root: &Raw) -> Result<Arc<Expr>, OleanError> {
        enum Step<'r> {
            Visit(&'r Raw),
            Build(&'r Raw),
        }
        // (field count, indices of Expr-typed fields) per ctor tag.
        const SHAPES: [(usize, &[usize]); 12] = [
            (1, &[]),        // 0 bvar(Nat)
            (1, &[]),        // 1 fvar(Name)
            (1, &[]),        // 2 mvar(Name)
            (1, &[]),        // 3 sort(Level)
            (2, &[]),        // 4 const(Name, List Level)
            (2, &[0, 1]),    // 5 app
            (3, &[1, 2]),    // 6 lam
            (3, &[1, 2]),    // 7 forallE
            (4, &[1, 2, 3]), // 8 letE
            (1, &[]),        // 9 lit
            (2, &[1]),       // 10 mdata
            (3, &[2]),       // 11 proj
        ];
        let mut stack = vec![Step::Visit(root)];
        while let Some(step) = stack.pop() {
            match step {
                Step::Visit(r) => {
                    if self.exprs.contains_key(&key(r)) {
                        continue;
                    }
                    let RawValue::Ctor { tag, fields, .. } = &**r else {
                        return Err(bad("Expr"));
                    };
                    let (nfields, expr_children) =
                        SHAPES.get(*tag as usize).ok_or_else(|| bad("Expr tag"))?;
                    if fields.len() != *nfields {
                        return Err(bad("Expr fields"));
                    }
                    stack.push(Step::Build(r));
                    for &i in *expr_children {
                        stack.push(Step::Visit(&fields[i]));
                    }
                }
                Step::Build(r) => {
                    let e = self.build_expr(r)?;
                    self.exprs.insert(key(r), e);
                }
            }
        }
        self.sub_expr(root)
    }

    fn build_expr(&mut self, r: &Raw) -> Result<Arc<Expr>, OleanError> {
        let RawValue::Ctor {
            tag,
            fields,
            scalars,
        } = &**r
        else {
            unreachable!()
        };
        // Scalar area: computed `data` u64 first (ignored; recomputed
        // in M1b), then u8 flags (kernel/expr.h:265 proves the order).
        let expr = match tag {
            0 => Expr::BVar {
                idx: nat(&fields[0])?,
            },
            1 => Expr::FVar {
                id: self.name(&fields[0])?,
            },
            2 => Expr::MVar {
                id: self.name(&fields[0])?,
            },
            3 => Expr::Sort {
                level: self.level(&fields[0])?,
            },
            4 => Expr::Const {
                name: self.name(&fields[0])?,
                levels: list(&fields[1])?
                    .into_iter()
                    .map(|l| self.level(l))
                    .collect::<Result<_, _>>()?,
            },
            5 => Expr::App {
                f: self.sub_expr(&fields[0])?,
                arg: self.sub_expr(&fields[1])?,
            },
            6 | 7 => {
                let binder_info = match scalars.get(8).copied() {
                    Some(0) => BinderInfo::Default,
                    Some(1) => BinderInfo::Implicit,
                    Some(2) => BinderInfo::StrictImplicit,
                    Some(3) => BinderInfo::InstImplicit,
                    _ => return Err(bad("BinderInfo")),
                };
                let (binder_name, binder_type, body) = (
                    self.name(&fields[0])?,
                    self.sub_expr(&fields[1])?,
                    self.sub_expr(&fields[2])?,
                );
                if *tag == 6 {
                    Expr::Lam {
                        binder_name,
                        binder_type,
                        body,
                        binder_info,
                    }
                } else {
                    Expr::ForallE {
                        binder_name,
                        binder_type,
                        body,
                        binder_info,
                    }
                }
            }
            8 => Expr::LetE {
                decl_name: self.name(&fields[0])?,
                ty: self.sub_expr(&fields[1])?,
                value: self.sub_expr(&fields[2])?,
                body: self.sub_expr(&fields[3])?,
                non_dep: boolean(scalars.get(8), "letE nondep")?,
            },
            9 => Expr::Lit(self.literal(&fields[0])?),
            10 => Expr::MData {
                data: self.kvmap(&fields[0])?,
                expr: self.sub_expr(&fields[1])?,
            },
            11 => Expr::Proj {
                type_name: self.name(&fields[0])?,
                idx: nat(&fields[1])?,
                structure: self.sub_expr(&fields[2])?,
            },
            _ => unreachable!("tag checked in Visit"),
        };
        Ok(Arc::new(expr))
    }

    fn literal(&mut self, r: &Raw) -> Result<Literal, OleanError> {
        match &**r {
            RawValue::Ctor { tag: 0, fields, .. } if fields.len() == 1 => {
                Ok(Literal::NatVal(nat(&fields[0])?))
            }
            RawValue::Ctor { tag: 1, fields, .. } if fields.len() == 1 => {
                Ok(Literal::StrVal(string(&fields[0])?))
            }
            _ => Err(bad("Literal")),
        }
    }

    /// KVMap ≅ List (Name × DataValue) (Data/KVMap.lean:71-73).
    fn kvmap(&mut self, r: &Raw) -> Result<KVMap, OleanError> {
        let mut entries = Vec::new();
        for pair in list(r)? {
            let (fields, _) = ctor(pair, 0, 2, "Prod")?;
            entries.push((self.name(&fields[0])?, self.data_value(&fields[1])?));
        }
        Ok(KVMap(entries))
    }

    /// DataValue (Data/KVMap.lean:18-25).
    fn data_value(&mut self, r: &Raw) -> Result<DataValue, OleanError> {
        match &**r {
            RawValue::Ctor { tag: 0, fields, .. } if fields.len() == 1 => {
                Ok(DataValue::OfString(string(&fields[0])?))
            }
            RawValue::Ctor {
                tag: 1,
                fields,
                scalars,
            } if fields.is_empty() => Ok(DataValue::OfBool(boolean(
                scalars.first(),
                "DataValue bool",
            )?)),
            RawValue::Ctor { tag: 2, fields, .. } if fields.len() == 1 => {
                Ok(DataValue::OfName(self.name(&fields[0])?))
            }
            RawValue::Ctor { tag: 3, fields, .. } if fields.len() == 1 => {
                Ok(DataValue::OfNat(nat(&fields[0])?))
            }
            RawValue::Ctor { tag: 4, fields, .. } if fields.len() == 1 => {
                Ok(DataValue::OfInt(int(&fields[0])?))
            }
            RawValue::Ctor { tag: 5, .. } => {
                // Syntax values drag in the whole Syntax type family;
                // the stdlib sweep decides if real kernel terms ever
                // carry them (spec: deferred).
                Err(OleanError::Unsupported {
                    what: "Syntax in expression metadata",
                })
            }
            _ => Err(bad("DataValue")),
        }
    }

    fn names(&mut self, items: Vec<&Raw>) -> Result<Vec<Arc<Name>>, OleanError> {
        items.into_iter().map(|n| self.name(n)).collect()
    }

    /// ConstantVal (Declaration.lean:95-99).
    fn constant_val(&mut self, r: &Raw) -> Result<ConstantVal, OleanError> {
        let (fields, _) = ctor(r, 0, 3, "ConstantVal")?;
        Ok(ConstantVal {
            name: self.name(&fields[0])?,
            level_params: self.names(list(&fields[1])?)?,
            ty: self.expr(&fields[2])?,
        })
    }

    /// ReducibilityHints (Declaration.lean:46-50).
    fn reducibility(&mut self, r: &Raw) -> Result<ReducibilityHints, OleanError> {
        match &**r {
            RawValue::Scalar(0) => Ok(ReducibilityHints::Opaque),
            RawValue::Scalar(1) => Ok(ReducibilityHints::Abbrev),
            RawValue::Ctor {
                tag: 2,
                fields,
                scalars,
            } if fields.is_empty() => {
                let bytes = scalars.get(..4).ok_or_else(|| bad("regular height"))?;
                Ok(ReducibilityHints::Regular(u32::from_le_bytes(
                    bytes.try_into().expect("4 bytes"),
                )))
            }
            _ => Err(bad("ReducibilityHints")),
        }
    }

    /// ConstantInfo (Declaration.lean:429-437) and its Val payloads.
    fn constant_info(&mut self, r: &Raw) -> Result<ConstantInfo, OleanError> {
        let RawValue::Ctor { tag, fields, .. } = &**r else {
            return Err(bad("ConstantInfo"));
        };
        if fields.len() != 1 {
            return Err(bad("ConstantInfo payload"));
        }
        let v = &fields[0];
        Ok(match tag {
            0 => {
                let (f, s) = ctor(v, 0, 1, "AxiomVal")?;
                ConstantInfo::Axiom(AxiomVal {
                    val: self.constant_val(&f[0])?,
                    is_unsafe: boolean(s.first(), "AxiomVal.isUnsafe")?,
                })
            }
            1 => {
                let (f, s) = ctor(v, 0, 4, "DefinitionVal")?;
                ConstantInfo::Defn(DefinitionVal {
                    val: self.constant_val(&f[0])?,
                    value: self.expr(&f[1])?,
                    hints: self.reducibility(&f[2])?,
                    safety: match s.first().copied() {
                        Some(0) => DefinitionSafety::Unsafe,
                        Some(1) => DefinitionSafety::Safe,
                        Some(2) => DefinitionSafety::Partial,
                        _ => return Err(bad("DefinitionSafety")),
                    },
                    all: self.names(list(&f[3])?)?,
                })
            }
            2 => {
                let (f, _) = ctor(v, 0, 3, "TheoremVal")?;
                ConstantInfo::Thm(TheoremVal {
                    val: self.constant_val(&f[0])?,
                    value: self.expr(&f[1])?,
                    all: self.names(list(&f[2])?)?,
                })
            }
            3 => {
                let (f, s) = ctor(v, 0, 3, "OpaqueVal")?;
                ConstantInfo::Opaque(OpaqueVal {
                    val: self.constant_val(&f[0])?,
                    value: self.expr(&f[1])?,
                    is_unsafe: boolean(s.first(), "OpaqueVal.isUnsafe")?,
                    all: self.names(list(&f[2])?)?,
                })
            }
            4 => {
                let (f, s) = ctor(v, 0, 1, "QuotVal")?;
                ConstantInfo::Quot(QuotVal {
                    val: self.constant_val(&f[0])?,
                    kind: match s.first().copied() {
                        Some(0) => QuotKind::Type,
                        Some(1) => QuotKind::Ctor,
                        Some(2) => QuotKind::Lift,
                        Some(3) => QuotKind::Ind,
                        _ => return Err(bad("QuotKind")),
                    },
                })
            }
            5 => {
                let (f, s) = ctor(v, 0, 6, "InductiveVal")?;
                ConstantInfo::Induct(InductiveVal {
                    val: self.constant_val(&f[0])?,
                    num_params: nat(&f[1])?,
                    num_indices: nat(&f[2])?,
                    all: self.names(list(&f[3])?)?,
                    ctors: self.names(list(&f[4])?)?,
                    num_nested: nat(&f[5])?,
                    is_rec: boolean(s.first(), "InductiveVal.isRec")?,
                    is_unsafe: boolean(s.get(1), "InductiveVal.isUnsafe")?,
                    is_reflexive: boolean(s.get(2), "InductiveVal.isReflexive")?,
                })
            }
            6 => {
                let (f, s) = ctor(v, 0, 5, "ConstructorVal")?;
                ConstantInfo::Ctor(ConstructorVal {
                    val: self.constant_val(&f[0])?,
                    induct: self.name(&f[1])?,
                    cidx: nat(&f[2])?,
                    num_params: nat(&f[3])?,
                    num_fields: nat(&f[4])?,
                    is_unsafe: boolean(s.first(), "ConstructorVal.isUnsafe")?,
                })
            }
            7 => {
                let (f, s) = ctor(v, 0, 7, "RecursorVal")?;
                let mut rules = Vec::new();
                for rule in list(&f[6])? {
                    let (rf, _) = ctor(rule, 0, 3, "RecursorRule")?;
                    rules.push(RecursorRule {
                        ctor: self.name(&rf[0])?,
                        nfields: nat(&rf[1])?,
                        rhs: self.expr(&rf[2])?,
                    });
                }
                ConstantInfo::Rec(RecursorVal {
                    val: self.constant_val(&f[0])?,
                    all: self.names(list(&f[1])?)?,
                    num_params: nat(&f[2])?,
                    num_indices: nat(&f[3])?,
                    num_motives: nat(&f[4])?,
                    num_minors: nat(&f[5])?,
                    rules,
                    k: boolean(s.first(), "RecursorVal.k")?,
                    is_unsafe: boolean(s.get(1), "RecursorVal.isUnsafe")?,
                })
            }
            _ => return Err(bad("ConstantInfo tag")),
        })
    }

    /// Import (Setup.lean:25-32).
    fn import(&mut self, r: &Raw) -> Result<crate::Import, OleanError> {
        let (f, s) = ctor(r, 0, 1, "Import")?;
        Ok(crate::Import {
            module: self.name(&f[0])?,
            import_all: boolean(s.first(), "Import.importAll")?,
            is_exported: boolean(s.get(1), "Import.isExported")?,
            is_meta: boolean(s.get(2), "Import.isMeta")?,
        })
    }

    /// ModuleData (Environment.lean:109-129).
    pub(crate) fn module_data(&mut self, root: &Raw) -> Result<crate::ModuleData, OleanError> {
        let (f, s) = ctor(root, 0, 5, "ModuleData")?;
        Ok(crate::ModuleData {
            is_module: boolean(s.first(), "ModuleData.isModule")?,
            imports: array(&f[0])?
                .iter()
                .map(|i| self.import(i))
                .collect::<Result<_, _>>()?,
            const_names: array(&f[1])?
                .iter()
                .map(|n| self.name(n))
                .collect::<Result<_, _>>()?,
            constants: array(&f[2])?
                .iter()
                .map(|c| self.constant_info(c))
                .collect::<Result<_, _>>()?,
            extra_const_names: array(&f[3])?
                .iter()
                .map(|n| self.name(n))
                .collect::<Result<_, _>>()?,
            num_entries: array(&f[4])?.len(),
        })
    }
}
