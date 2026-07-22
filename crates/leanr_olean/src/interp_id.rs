//! Phase B, id-emitting (term-bank phase 3): interpret the validated
//! [`RawValue`] DAG directly into term-bank ids. This is the ONLY
//! decode path (the differential-gated Arc path it was checked against
//! is deleted; see `interp.rs`'s module doc) — decoding IS interning,
//! with per-type memos mapping one file offset to one id. `Syntax`
//! subtrees remain Arc trees (opaque kernel payload, ptr-eq semantics —
//! spec non-goal) and are decoded by the embedded Arc [`Interp`], which
//! also supplies `Name` decoding for `Import.module`.

use std::collections::HashMap;

use leanr_kernel::bank::pools::DataValueRow;
use leanr_kernel::bank::{ExprId, KVMapId, LevelId, NameId, Store};
use leanr_kernel::{
    AxiomVal, BinderInfo, ConstantInfo, ConstantVal, ConstructorVal, DefinitionSafety,
    DefinitionVal, InductiveVal, OpaqueVal, QuotKind, QuotVal, RecursorRule, RecursorVal,
    TheoremVal,
};

use crate::interp::{
    array, bad, boolean, ctor, int, key, list, nat, reducibility, string, Interp, Raw,
};
use crate::raw::RawValue;
use crate::OleanError;

pub(crate) struct InterpId<'s> {
    st: &'s mut Store,
    /// Arc-side interpreter for the surviving Arc-tree positions:
    /// `Syntax` payloads (opaque, ptr-eq) and `Import.module` names
    /// (the loader keys its DFS and file resolution on `Arc<Name>`).
    arc: Interp,
    names: HashMap<*const RawValue, Option<NameId>>,
    levels: HashMap<*const RawValue, LevelId>,
    exprs: HashMap<*const RawValue, ExprId>,
}

impl<'s> InterpId<'s> {
    pub(crate) fn new(st: &'s mut Store) -> InterpId<'s> {
        InterpId {
            st,
            arc: Interp::new(),
            names: HashMap::new(),
            levels: HashMap::new(),
            exprs: HashMap::new(),
        }
    }

    /// Name (Init/Prelude.lean:4693-4717): same iterative chain walk as
    /// `Interp::name`; `None` = anonymous (the bank has no row for it).
    fn name(&mut self, r: &Raw) -> Result<Option<NameId>, OleanError> {
        let mut chain: Vec<&Raw> = Vec::new();
        let mut cur = r;
        let mut built: Option<NameId> = loop {
            if let RawValue::Scalar(0) = &**cur {
                break None;
            }
            if let Some(&n) = self.names.get(&key(cur)) {
                break n;
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
            let id = match tag {
                1 => {
                    let part = self.st.intern_str(None, &string(&fields[1])?)?;
                    self.st.name_str(None, built, part)?
                }
                2 => {
                    let part = self.st.intern_nat(None, &nat(&fields[1])?)?;
                    self.st.name_num(None, built, part)?
                }
                _ => unreachable!(),
            };
            built = Some(id);
            self.names.insert(key(node), built);
        }
        Ok(built)
    }

    /// Declaration-position name: never anonymous in legitimate data
    /// (same posture as `decl.rs`'s `intern_name_req` — reject, don't
    /// assert).
    fn name_req(&mut self, r: &Raw) -> Result<NameId, OleanError> {
        self.name(r)?.ok_or_else(|| bad("non-anonymous Name"))
    }

    fn sub_level(&mut self, r: &Raw) -> Result<LevelId, OleanError> {
        if let RawValue::Scalar(0) = &**r {
            return Ok(self.st.level_zero(None)?);
        }
        self.levels
            .get(&key(r))
            .copied()
            .ok_or_else(|| bad("Level subterm"))
    }

    /// Level (Level.lean:90-103): explicit-stack post-order, identical
    /// shape/tag validation to `Interp::level`.
    fn level(&mut self, root: &Raw) -> Result<LevelId, OleanError> {
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
                    let id = match tag {
                        1 => {
                            let a = self.sub_level(&fields[0])?;
                            self.st.level_succ(None, a)?
                        }
                        2 => {
                            let a = self.sub_level(&fields[0])?;
                            let b = self.sub_level(&fields[1])?;
                            self.st.level_max(None, a, b)?
                        }
                        3 => {
                            let a = self.sub_level(&fields[0])?;
                            let b = self.sub_level(&fields[1])?;
                            self.st.level_imax(None, a, b)?
                        }
                        4 => {
                            let n = self.name(&fields[0])?;
                            self.st.level_param(None, n)?
                        }
                        5 => {
                            let n = self.name(&fields[0])?;
                            self.st.level_mvar(None, n)?
                        }
                        _ => unreachable!(),
                    };
                    self.levels.insert(key(r), id);
                }
            }
        }
        self.sub_level(root)
    }

    fn sub_expr(&self, r: &Raw) -> Result<ExprId, OleanError> {
        self.exprs
            .get(&key(r))
            .copied()
            .ok_or_else(|| bad("Expr subterm"))
    }

    /// Expr (Expr.lean:321-471): explicit-stack post-order over the
    /// Expr-typed fields; same SHAPES table as `Interp::expr`.
    fn expr(&mut self, root: &Raw) -> Result<ExprId, OleanError> {
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

    fn build_expr(&mut self, r: &Raw) -> Result<ExprId, OleanError> {
        let RawValue::Ctor {
            tag,
            fields,
            scalars,
        } = &**r
        else {
            unreachable!()
        };
        // Scalar area: computed `data` u64 first (ignored; the bank's
        // row constructors recompute an equivalent `ExprData`), then
        // u8 flags (kernel/expr.h:265 proves the order).
        let expr: ExprId = match tag {
            0 => self.st.expr_bvar(None, &nat(&fields[0])?)?,
            1 => {
                let n = self.name(&fields[0])?;
                self.st.expr_fvar(None, n)?
            }
            2 => {
                let n = self.name(&fields[0])?;
                self.st.expr_mvar(None, n)?
            }
            3 => {
                let l = self.level(&fields[0])?;
                self.st.expr_sort(None, l)?
            }
            4 => {
                let n = self.name(&fields[0])?;
                let levels = list(&fields[1])?
                    .into_iter()
                    .map(|l| self.level(l))
                    .collect::<Result<Vec<_>, _>>()?;
                let ls = self.st.intern_level_list(None, &levels)?;
                self.st.expr_const(None, n, ls)?
            }
            5 => {
                let f = self.sub_expr(&fields[0])?;
                let arg = self.sub_expr(&fields[1])?;
                self.st.expr_app(None, f, arg)?
            }
            6 | 7 => {
                let binder_info = match scalars.get(8).copied() {
                    Some(0) => BinderInfo::Default,
                    Some(1) => BinderInfo::Implicit,
                    Some(2) => BinderInfo::StrictImplicit,
                    Some(3) => BinderInfo::InstImplicit,
                    _ => return Err(bad("BinderInfo")),
                };
                let binder_name = self.name(&fields[0])?;
                let binder_type = self.sub_expr(&fields[1])?;
                let body = self.sub_expr(&fields[2])?;
                if *tag == 6 {
                    self.st
                        .expr_lam(None, binder_name, binder_type, body, binder_info)?
                } else {
                    self.st
                        .expr_forall(None, binder_name, binder_type, body, binder_info)?
                }
            }
            8 => {
                let decl_name = self.name(&fields[0])?;
                let ty = self.sub_expr(&fields[1])?;
                let value = self.sub_expr(&fields[2])?;
                let body = self.sub_expr(&fields[3])?;
                let non_dep = boolean(scalars.get(8), "letE nondep")?;
                self.st
                    .expr_let(None, decl_name, ty, value, body, non_dep)?
            }
            9 => match &*fields[0] {
                RawValue::Ctor {
                    tag: 0, fields: lf, ..
                } if lf.len() == 1 => self.st.expr_lit_nat(None, &nat(&lf[0])?)?,
                RawValue::Ctor {
                    tag: 1, fields: lf, ..
                } if lf.len() == 1 => self.st.expr_lit_str(None, &string(&lf[0])?)?,
                _ => return Err(bad("Literal")),
            },
            10 => {
                let data = self.kvmap(&fields[0])?;
                let sub = self.sub_expr(&fields[1])?;
                self.st.expr_mdata(None, data, sub)?
            }
            11 => {
                let type_name = self.name(&fields[0])?;
                let idx = nat(&fields[1])?;
                let structure = self.sub_expr(&fields[2])?;
                self.st.expr_proj(None, type_name, &idx, structure)?
            }
            _ => unreachable!("tag checked in Visit"),
        };
        Ok(expr)
    }

    /// KVMap ≅ List (Name × DataValue) (Data/KVMap.lean:71-73).
    fn kvmap(&mut self, r: &Raw) -> Result<KVMapId, OleanError> {
        let mut entries: Vec<(Option<NameId>, DataValueRow)> = Vec::new();
        for pair in list(r)? {
            let (fields, _) = ctor(pair, 0, 2, "Prod")?;
            let n = self.name(&fields[0])?;
            let v = self.data_value(&fields[1])?;
            entries.push((n, v));
        }
        Ok(self.st.intern_kvmap_rows(None, entries)?)
    }

    /// DataValue (Data/KVMap.lean:18-25). `OfSyntax` stays an Arc tree
    /// decoded by the embedded Arc interpreter (opaque payload,
    /// ptr-eq semantics).
    fn data_value(&mut self, r: &Raw) -> Result<DataValueRow, OleanError> {
        match &**r {
            RawValue::Ctor { tag: 0, fields, .. } if fields.len() == 1 => Ok(DataValueRow::Str(
                self.st.intern_str(None, &string(&fields[0])?)?,
            )),
            RawValue::Ctor {
                tag: 1,
                fields,
                scalars,
            } if fields.is_empty() => Ok(DataValueRow::Bool(boolean(
                scalars.first(),
                "DataValue bool",
            )?)),
            RawValue::Ctor { tag: 2, fields, .. } if fields.len() == 1 => {
                Ok(DataValueRow::Name(self.name(&fields[0])?))
            }
            RawValue::Ctor { tag: 3, fields, .. } if fields.len() == 1 => Ok(DataValueRow::Nat(
                self.st.intern_nat(None, &nat(&fields[0])?)?,
            )),
            RawValue::Ctor { tag: 4, fields, .. } if fields.len() == 1 => Ok(DataValueRow::Int(
                self.st.intern_int(None, &int(&fields[0])?)?,
            )),
            RawValue::Ctor { tag: 5, fields, .. } if fields.len() == 1 => {
                Ok(DataValueRow::Syntax(self.arc.syntax(&fields[0])?))
            }
            _ => Err(bad("DataValue")),
        }
    }

    fn names(&mut self, items: Vec<&Raw>) -> Result<Vec<NameId>, OleanError> {
        items.into_iter().map(|n| self.name_req(n)).collect()
    }

    /// ConstantVal (Declaration.lean:95-99).
    fn constant_val(&mut self, r: &Raw) -> Result<ConstantVal, OleanError> {
        let (fields, _) = ctor(r, 0, 3, "ConstantVal")?;
        Ok(ConstantVal {
            name: self.name_req(&fields[0])?,
            level_params: self.names(list(&fields[1])?)?,
            ty: self.expr(&fields[2])?,
        })
    }

    /// ConstantInfo (Declaration.lean:429-437) and its Val payloads —
    /// arm-for-arm the same shapes as `Interp::constant_info`.
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
                    hints: reducibility(&f[2])?,
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
                    induct: self.name_req(&f[1])?,
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
                        ctor: self.name_req(&rf[0])?,
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

    /// Import (Setup.lean:25-32). `Import.module` stays `Arc<Name>`:
    /// the loader keys its DFS and file resolution on it.
    fn import(&mut self, r: &Raw) -> Result<crate::Import, OleanError> {
        let (f, s) = ctor(r, 0, 1, "Import")?;
        Ok(crate::Import {
            module: self.arc.name(&f[0])?,
            import_all: boolean(s.first(), "Import.importAll")?,
            is_exported: boolean(s.get(1), "Import.isExported")?,
            is_meta: boolean(s.get(2), "Import.isMeta")?,
        })
    }

    /// oracle: ScopedEnvExtension.Entry — tag 0 global(v), tag 1 scoped(ns, v).
    fn scoped_parser_entry(&mut self, r: &Raw) -> Result<crate::ScopedParserEntry, OleanError> {
        let RawValue::Ctor { tag, fields, .. } = &**r else {
            return Err(bad("ScopedEnvExtension.Entry"));
        };
        let (scope, payload) = match (tag, fields.len()) {
            (0, 1) => (crate::EntryScope::Global, &fields[0]),
            (1, 2) => (
                crate::EntryScope::Scoped(self.name_req(&fields[0])?),
                &fields[1],
            ),
            _ => return Err(bad("ScopedEnvExtension.Entry")),
        };
        Ok(crate::ScopedParserEntry {
            scope,
            entry: self.parser_entry(payload)?,
        })
    }

    /// oracle: ParserExtension.OLeanEntry (Extension.lean:57-62), tag order.
    ///
    /// Empirical pin (NotaDep.olean, via a temporary eprintln dumping each
    /// entry's `(tag, fields.len(), scalars)` before the `match`): the
    /// `widget` category entry decoded as `Ctor{tag:2, fields:2,
    /// scalars:[0,0,0,0,0,0,0,0]}` — `behavior` (`LeadingIdentBehavior`)
    /// arrives as a SCALAR byte (the enum discriminant at `scalars[0]`,
    /// padded to a word), not a boxed pointer field. This matches the
    /// brief's first hypothesis and the `DefinitionSafety`/`QuotKind`
    /// pattern elsewhere in this file, not the boxed-`Scalar`-field
    /// pattern. Also confirmed: the raw `ModuleData.entries` pair is
    /// `Ctor{tag:0, fields:2}` (`Name × Array EnvExtensionEntry`) and the
    /// `ScopedEnvExtension.Entry` wrapper is `Ctor{tag:0, fields:1}`
    /// (global) / `Ctor{tag:1, fields:2}` (scoped) — both as hypothesized,
    /// needing no adjustment.
    fn parser_entry(&mut self, r: &Raw) -> Result<crate::ParserEntry, OleanError> {
        let RawValue::Ctor {
            tag,
            fields,
            scalars,
        } = &**r
        else {
            return Err(bad("ParserExtension.OLeanEntry"));
        };
        match (tag, fields.len()) {
            (0, 1) => Ok(crate::ParserEntry::Token(string(&fields[0])?)),
            (1, 1) => Ok(crate::ParserEntry::Kind(self.name_req(&fields[0])?)),
            (2, 2) => Ok(crate::ParserEntry::Category {
                cat: self.name_req(&fields[0])?,
                decl: self.name_req(&fields[1])?,
                behavior: match scalars.first().copied() {
                    Some(0) => crate::CatBehavior::Default,
                    Some(1) => crate::CatBehavior::Symbol,
                    Some(2) => crate::CatBehavior::Both,
                    _ => return Err(bad("LeadingIdentBehavior")),
                },
            }),
            (3, 3) => {
                let _prio = nat(&fields[2])?; // validated, dropped
                Ok(crate::ParserEntry::Parser {
                    cat: self.name_req(&fields[0])?,
                    decl: self.name_req(&fields[1])?,
                })
            }
            _ => Err(bad("ParserExtension.OLeanEntry")),
        }
    }

    /// oracle: `ReducibilityStatus` (ReducibilityAttrs.lean:40-42).
    /// Arrives as a BOXED immediate, not in the ctor's scalar area:
    /// `Prod`'s fields are polymorphic, so a nullary ctor in that
    /// position is a `RawValue::Scalar(tag)`. (Contrast `parser_entry`'s
    /// `LeadingIdentBehavior`, which is a monomorphic field and so is
    /// unboxed into `scalars`.) Shape pinned empirically against
    /// Reducibility.olean: a temporary probe printed each
    /// `reducibilityCore` pair's second field, observing
    /// `RawValue::Scalar(n)` for n in {0,2,3,4} (reducible, irreducible,
    /// implicitReducible, instanceReducible — matching the fixture's
    /// four attributed constants), confirming the brief's hypothesis
    /// with no adaptation needed.
    ///
    /// Tag 1 (`Semireducible`) is verified against the oracle's
    /// constructor declaration order (ReducibilityAttrs.lean:41) but is
    /// the one cell NOT pinned by fixture bytes: no ordinary fixture
    /// can produce an explicit tag-1 entry. The oracle's validator
    /// unconditionally rejects a global `[semireducible]` attribute
    /// application (ReducibilityAttrs.lean's `validate`, the
    /// `.semireducible`/`.global` arm), and `local`-kind entries never
    /// serialize into the `.olean` (`ScopedEnvExtension.addCore`'s
    /// `.local` branch calls `addLocalEntry`, which never joins the
    /// `newEntries` list `exportEntriesFn` reads). The one escape
    /// hatch is `set_option allowUnsafeReducibility true`, which skips
    /// the validator — how tag-1 entries occur in the wild (Mathlib
    /// uses it); a fixture via that route is a plan-2 candidate.
    fn reducibility_status(r: &Raw) -> Result<crate::ReducibilityStatus, OleanError> {
        match &**r {
            RawValue::Scalar(0) => Ok(crate::ReducibilityStatus::Reducible),
            // See the doc comment above: not pinned by fixture bytes.
            RawValue::Scalar(1) => Ok(crate::ReducibilityStatus::Semireducible),
            RawValue::Scalar(2) => Ok(crate::ReducibilityStatus::Irreducible),
            RawValue::Scalar(3) => Ok(crate::ReducibilityStatus::ImplicitReducible),
            RawValue::Scalar(4) => Ok(crate::ReducibilityStatus::InstanceReducible),
            _ => Err(bad("ReducibilityStatus")),
        }
    }

    /// `Name × ReducibilityStatus` — a bare 2-field `Prod` (tag 0).
    fn reducibility_pair(
        &mut self,
        r: &Raw,
    ) -> Result<(NameId, crate::ReducibilityStatus), OleanError> {
        let (f, _) = ctor(r, 0, 2, "Name × ReducibilityStatus")?;
        Ok((self.name_req(&f[0])?, Self::reducibility_status(&f[1])?))
    }

    /// `Option Nat` arriving in a monomorphic-but-polymorphically-typed
    /// field position: `none` is a boxed nullary tag (`RawValue::Scalar(0)`,
    /// same reasoning as `reducibility_status`'s doc comment — `Option`
    /// is itself polymorphic, so its `none` constructor is a boxed
    /// immediate here, not unboxed into a `scalars` byte area), `some x`
    /// is `Ctor { tag: 1, fields: [x] }`. Pinned empirically against
    /// `Matcher.olean`'s `uElimPos?` field (`MatcherInfo.lean:58-61):
    /// both fixture matchers eliminate into `N` (a `Type`, not `Prop`),
    /// so both carry `some 0` (the matcher's motive is universe-generic,
    /// position 0 of its level params) — `none` is not fixture-pinned by
    /// this file, only verified against the oracle's tag-order
    /// convention (`some` is Option's second declared constructor, tag 1).
    fn opt_nat(r: &Raw) -> Result<Option<leanr_kernel::Nat>, OleanError> {
        match &**r {
            RawValue::Scalar(0) => Ok(None),
            RawValue::Ctor { tag: 1, fields, .. } if fields.len() == 1 => {
                Ok(Some(nat(&fields[0])?))
            }
            _ => Err(bad("Option Nat")),
        }
    }

    /// `Option Name` arriving the same boxed-nullary way as `opt_nat`
    /// above (`Option` is polymorphic, so its `none` is a boxed
    /// immediate). Used for `DiscrInfo.hName?` — see `matcher_entry`'s
    /// doc comment for why `DiscrInfo` itself does not appear as a
    /// separate wrapper ctor here.
    fn opt_name(&mut self, r: &Raw) -> Result<Option<NameId>, OleanError> {
        match &**r {
            RawValue::Scalar(0) => Ok(None),
            RawValue::Ctor { tag: 1, fields, .. } if fields.len() == 1 => {
                Ok(self.name(&fields[0])?)
            }
            _ => Err(bad("Option Name")),
        }
    }

    /// oracle: `Lean.Meta.Match.Extension.Entry` — 2-field ctor
    /// `{ name, info : MatcherInfo }`; `MatcherInfo` (MatcherInfo.lean:52-68)
    /// is a 6-field ctor (numParams, numDiscrs, altInfos, uElimPos?,
    /// discrInfos, overlaps) — NOT 5 as the task-1 brief's schematic
    /// listed; the brief predated checking the oracle file directly and
    /// omitted the trailing `overlaps : Overlaps` field. `overlaps` is
    /// validated only by the exact-field-count `ctor` check below and is
    /// never read (see `MatcherEntry`'s doc comment).
    ///
    /// Shape pinned empirically against `Matcher.olean` (temporary
    /// `eprintln` probe over each field, per-field and one level into
    /// each nested ctor/array):
    /// - `numParams`/`numDiscrs`: plain `Nat`s riding directly in the
    ///   ctor's pointer `fields` (as `RawValue::Scalar`/`BigInt`, decoded
    ///   by the free `nat()` helper) — NOT in the `scalars` byte area.
    ///   (Contrast `AltParamInfo` below: monomorphic-struct-position
    ///   `Nat`s still decode via plain `nat()`, since `Nat` boxes small
    ///   values as scalars regardless of the enclosing struct's
    ///   polymorphism — only enum/bool DISCRIMINANTS move between the
    ///   scalar area and boxed-immediate positions depending on whether
    ///   the field's static type is polymorphic.)
    /// - `altInfos`: `RawValue::Array` of `AltParamInfo` ctors, each
    ///   `Ctor { tag: 0, fields: [numFields, numOverlaps], scalars: [hasUnitThunk, ..] }`
    ///   — `hasUnitThunk : Bool` rides in `scalars[0]` (monomorphic bool
    ///   field, same pattern as `RecursorVal.k`/`InductiveVal.isRec`),
    ///   while the two `Nat` fields are boxed pointer fields.
    /// - `uElimPos?`: boxed-nullary `Option Nat` (see `opt_nat` above);
    ///   both fixture matchers observed `some 0`.
    /// - `discrInfos`: `RawValue::Array` whose elements are `Option Name`
    ///   values DIRECTLY (`RawValue::Scalar(0)` in this fixture, one per
    ///   discriminant) — NOT a `DiscrInfo { hName? }` wrapper ctor. This
    ///   deviates from the brief's schematic (`ctor(d, 0, 1, "DiscrInfo")`
    ///   then read field 0): the oracle's runtime unboxes a single-field
    ///   structure to its one field's own representation (no allocation),
    ///   and `.olean` serialization mirrors that runtime object graph, so
    ///   `DiscrInfo`'s wrapper never appears on the wire.
    /// - `overlaps` (field 5): a `Ctor { tag: 0, fields: [2 ..] }` (the
    ///   `Overlaps`/`Std.HashMap` internals) — confirmed present (so the
    ///   ctor's exact-field-count check must ask for 6, not 5) but its
    ///   contents are never decoded.
    fn matcher_entry(&mut self, r: &Raw) -> Result<crate::MatcherEntry, OleanError> {
        let (f, _) = ctor(r, 0, 2, "Match.Extension.Entry")?;
        let name = self.name_req(&f[0])?;
        let (mf, _) = ctor(&f[1], 0, 6, "MatcherInfo")?;
        let num_params = nat(&mf[0])?;
        let num_discrs = nat(&mf[1])?;
        let mut alt_infos = Vec::new();
        for a in array(&mf[2])? {
            let (af, as_) = ctor(a, 0, 2, "AltParamInfo")?;
            alt_infos.push(crate::MatcherAltInfo {
                num_fields: nat(&af[0])?,
                num_overlaps: nat(&af[1])?,
                has_unit_thunk: boolean(as_.first(), "AltParamInfo.hasUnitThunk")?,
            });
        }
        let u_elim_pos = Self::opt_nat(&mf[3])?;
        let mut discr_infos = Vec::new();
        for d in array(&mf[4])? {
            discr_infos.push(self.opt_name(d)?);
        }
        Ok(crate::MatcherEntry {
            name,
            num_params,
            num_discrs,
            alt_infos,
            u_elim_pos,
            discr_infos,
        })
    }

    /// `Lean.Meta.DiscrTree.Key` (Meta/DiscrTree/Types.lean:16-24,
    /// v4.33.0-rc1) — see `crate::DiscrKey`'s doc comment for the full
    /// ctor-tag transcription and the brief-vs-source disagreement (no
    /// `Bvar`/`Sort` ctor exists on `Key`). Nullary ctors (`star`,
    /// `other`, `arrow`) arrive as boxed scalar immediates
    /// (`RawValue::Scalar(tag)`); the rest as `Ctor { tag, fields }`,
    /// same posture as `reducibility_status`/`matcher_entry`. Dispatched
    /// from `module_data`'s `Lean.Meta.instanceExtension` arm
    /// (Task A3).
    fn discr_key(&mut self, r: &Raw) -> Result<crate::DiscrKey, OleanError> {
        use crate::DiscrKey;
        // Untrusted-bignum arity/index: never truncate via `as usize`
        // (see `Nat::to_usize`'s doc) — a value too large to fit is a
        // shape error, not silently wrapped.
        fn nat_usize(r: &Raw) -> Result<usize, OleanError> {
            nat(r)?.to_usize().ok_or_else(|| bad("DiscrTree.Key Nat"))
        }
        match &**r {
            RawValue::Scalar(0) => Ok(DiscrKey::Star),
            RawValue::Scalar(1) => Ok(DiscrKey::Other),
            RawValue::Scalar(5) => Ok(DiscrKey::Arrow),
            RawValue::Ctor { tag: 2, fields, .. } if fields.len() == 1 => {
                match &*fields[0] {
                    RawValue::Ctor {
                        tag: 0, fields: lf, ..
                    } if lf.len() == 1 => Ok(DiscrKey::Lit(leanr_kernel::Literal::NatVal(nat(
                        &lf[0],
                    )?))),
                    RawValue::Ctor {
                        tag: 1, fields: lf, ..
                    } if lf.len() == 1 => Ok(DiscrKey::Lit(leanr_kernel::Literal::StrVal(
                        string(&lf[0])?,
                    ))),
                    _ => Err(bad("DiscrTree.Key.lit Literal")),
                }
            }
            RawValue::Ctor { tag: 3, fields, .. } if fields.len() == 2 => {
                // fields[0] is the fvar's FVarId, unboxed to its `Name`
                // field on the wire (same as `Expr.fvar`'s field 0);
                // identity is not stable across serialization, so only
                // shape is validated and the name itself is discarded.
                let _ = self.name(&fields[0])?;
                Ok(DiscrKey::Fvar {
                    arity: nat_usize(&fields[1])?,
                })
            }
            RawValue::Ctor { tag: 4, fields, .. } if fields.len() == 2 => Ok(DiscrKey::Const {
                name: self.name_req(&fields[0])?,
                arity: nat_usize(&fields[1])?,
            }),
            RawValue::Ctor { tag: 6, fields, .. } if fields.len() == 3 => Ok(DiscrKey::Proj {
                structure: self.name_req(&fields[0])?,
                index: nat_usize(&fields[1])?,
                arity: nat_usize(&fields[2])?,
            }),
            _ => Err(bad("DiscrTree.Key")),
        }
    }

    /// `Lean.Meta.InstanceEntry` (Meta/Instances.lean:50-66, pinned
    /// toolchain v4.33.0-rc1): six DECLARED fields —
    /// `keys, val, priority, globalName?, synthOrder, attrKind` — not
    /// the five-field `keys, val, priority, globalName?, attrKind`
    /// shape an earlier draft of this plan expected (that draft omitted
    /// `synthOrder`).
    ///
    /// On the WIRE, though, this is a 5-pointer-field ctor, not 6: a
    /// probe over `Instances.olean`'s fixture entries showed
    /// `Ctor { tag: 0, fields: [5 ..], .. }` for every decoded
    /// `InstanceEntry`. `attrKind : AttributeKind` (3 nullary
    /// constructors — `Attributes.lean:44-45`) is scalar-representable
    /// as a concrete (non-generic) field, so the compiler packs it as a
    /// raw byte in the ctor's `scalars` tail rather than a 6th boxed
    /// pointer field — the same mechanism already pinned by
    /// `ModuleData.isModule`'s `bool` (see `module_data`'s `s.first()`
    /// read below). This differs from `reducibility_pair`'s
    /// `ReducibilityStatus` field, which stays a boxed `Scalar(tag)`
    /// pointer: that field sits in a *generic* `Prod α β`, whose
    /// compiled ctor can't specialize per-instantiation and so always
    /// keeps every field pointer-sized. `attrKind` is validated by
    /// checking the scalar tail holds one in-range byte, but its value
    /// is never read: no leanr consumer needs `getInstanceAttrKind`.
    /// `synthOrder` (field 4) IS decoded and returned (controller
    /// decision: PR-B reads the toolchain's own serialized argument
    /// order rather than re-transcribing `computeSynthOrder`).
    fn instance_entry_payload(
        &mut self,
        scope: crate::EntryScope,
        r: &Raw,
    ) -> Result<crate::InstanceEntry, OleanError> {
        // Untrusted-bignum priority/synthOrder entries: never truncate
        // via `as usize` (see `Nat::to_usize`'s doc and `discr_key`'s
        // identical posture above) — a value too large to fit is a
        // shape error, not silently wrapped.
        fn nat_usize(r: &Raw) -> Result<usize, OleanError> {
            nat(r)?.to_usize().ok_or_else(|| bad("InstanceEntry Nat"))
        }
        let (f, s) = ctor(r, 0, 5, "InstanceEntry")?;
        match s.first() {
            Some(0..=2) => {}
            _ => return Err(bad("InstanceEntry.attrKind")),
        }
        let keys = array(&f[0])?
            .iter()
            .map(|k| self.discr_key(k))
            .collect::<Result<_, _>>()?;
        let val = self.expr(&f[1])?;
        let priority = nat_usize(&f[2])?;
        let global_name = self.opt_name(&f[3])?;
        let synth_order = array(&f[4])?
            .iter()
            .map(nat_usize)
            .collect::<Result<_, _>>()?;
        Ok(crate::InstanceEntry {
            scope,
            keys,
            val,
            priority,
            synth_order,
            global_name,
        })
    }

    /// ModuleData (Environment.lean:109-129).
    pub(crate) fn module_data(&mut self, root: &Raw) -> Result<crate::ModuleData, OleanError> {
        let (f, s) = ctor(root, 0, 5, "ModuleData")?;
        // entries : Array (Name × Array EnvExtensionEntry). Only the
        // parserExtension and reducibility pairs are decoded (M3b2a,
        // M4a); others stay opaque.
        let mut parser_entries = Vec::new();
        let mut reducibility = Vec::new();
        let mut matchers = Vec::new();
        let mut instances = Vec::new();
        for pair in array(&f[4])? {
            let (pf, _) = ctor(pair, 0, 2, "ModuleData.entries pair")?;
            let ext_name = self.name(&pf[0])?;
            match self.st.to_name(None, ext_name).to_string().as_str() {
                "Lean.Parser.parserExtension" => {
                    for e in array(&pf[1])? {
                        parser_entries.push(self.scoped_parser_entry(e)?);
                    }
                }
                // Unwrapped `Name × ReducibilityStatus`, sorted by
                // `Name.quickLt`. No `ScopedEnvExtension.Entry` wrapper:
                // this is a plain `registerPersistentEnvExtension`.
                "reducibilityCore" => {
                    for e in array(&pf[1])? {
                        let (name, status) = self.reducibility_pair(e)?;
                        reducibility.push(crate::ReducibilityEntry {
                            scope: crate::EntryScope::Global,
                            name,
                            status,
                        });
                    }
                }
                // Wrapped in `ScopedEnvExtension.Entry`: tag 0 global(v),
                // tag 1 scoped(ns, v). Usually empty in practice, but
                // both constructors are decoded rather than assumed away.
                "reducibilityExtra" => {
                    for e in array(&pf[1])? {
                        let RawValue::Ctor { tag, fields, .. } = &**e else {
                            return Err(bad("ScopedEnvExtension.Entry"));
                        };
                        let (scope, payload) = match (tag, fields.len()) {
                            (0, 1) => (crate::EntryScope::Global, &fields[0]),
                            (1, 2) => (
                                crate::EntryScope::Scoped(self.name_req(&fields[0])?),
                                &fields[1],
                            ),
                            _ => return Err(bad("ScopedEnvExtension.Entry")),
                        };
                        let (name, status) = self.reducibility_pair(payload)?;
                        reducibility.push(crate::ReducibilityEntry {
                            scope,
                            name,
                            status,
                        });
                    }
                }
                // SimplePersistentEnvExtension: entries are bare
                // Entry ctors, no scoped wrapper (like reducibilityCore).
                "Lean.Meta.Match.Extension.extension" => {
                    for e in array(&pf[1])? {
                        matchers.push(self.matcher_entry(e)?);
                    }
                }
                // Wrapped in `ScopedEnvExtension.Entry`, same tag-0
                // global(v) / tag-1 scoped(ns, v) shape as
                // `reducibilityExtra` above (mirrored verbatim).
                "Lean.Meta.instanceExtension" => {
                    for e in array(&pf[1])? {
                        let RawValue::Ctor { tag, fields, .. } = &**e else {
                            return Err(bad("ScopedEnvExtension.Entry"));
                        };
                        let (scope, payload) = match (tag, fields.len()) {
                            (0, 1) => (crate::EntryScope::Global, &fields[0]),
                            (1, 2) => (
                                crate::EntryScope::Scoped(self.name_req(&fields[0])?),
                                &fields[1],
                            ),
                            _ => return Err(bad("ScopedEnvExtension.Entry")),
                        };
                        instances.push(self.instance_entry_payload(scope, payload)?);
                    }
                }
                _ => continue,
            }
        }
        Ok(crate::ModuleData {
            is_module: boolean(s.first(), "ModuleData.isModule")?,
            imports: array(&f[0])?
                .iter()
                .map(|i| self.import(i))
                .collect::<Result<_, _>>()?,
            const_names: array(&f[1])?
                .iter()
                .map(|n| self.name_req(n))
                .collect::<Result<_, _>>()?,
            constants: array(&f[2])?
                .iter()
                .map(|c| self.constant_info(c))
                .collect::<Result<_, _>>()?,
            extra_const_names: array(&f[3])?
                .iter()
                .map(|n| self.name_req(n))
                .collect::<Result<_, _>>()?,
            num_entries: array(&f[4])?.len(),
            parser_entries,
            reducibility,
            matchers,
            instances,
        })
    }
}
