//! Phase B: interpret the validated [`RawValue`] DAG into the surviving
//! `leanr_kernel` Arc-tree positions. Since the direct-to-id decode
//! flip (term-bank phase 3, `interp_id.rs`), this module no longer
//! decodes `Expr`/`Level`/`ConstantInfo` at all — those go straight to
//! bank ids via `InterpId`. What's left here is the Arc-tree "opaque
//! payload" territory `InterpId` embeds an [`Interp`] for: `Syntax`
//! (ptr-eq semantics, ConstantInfo(-adjacent) but out of the spec's
//! goals — kvmap's `DataValue::OfSyntax`) and `Name` (needed both for
//! `Syntax`'s own fields and for `Import.module`, which the loader keys
//! its DFS and file resolution on via `Arc<Name>`). Phase A already
//! bounds-checked every byte, so this module only checks *shape*.
//!
//! Sharing: per-type memos keyed by raw node address map one file
//! offset to one `Arc`, preserving the file's DAG structure (the
//! oracle max-shares aggressively; naive tree conversion would explode
//! memory). `Syntax` conversion is an explicit-stack post-order walk
//! because node depth is attacker-controlled.

use std::collections::HashMap;
use std::sync::Arc;

use leanr_kernel::{Int, Name, Nat, Preresolved, ReducibilityHints, SourceInfo, Substring, Syntax};
use num_bigint::{BigInt, BigUint};

use crate::raw::RawValue;
use crate::OleanError;

pub(crate) type Raw = Arc<RawValue>;

pub(crate) fn key(r: &Raw) -> *const RawValue {
    Arc::as_ptr(r)
}

pub(crate) fn bad(expected: &'static str) -> OleanError {
    OleanError::BadShape { expected }
}

/// Exact-count ctor accessor: `m_other` is the writer's exact pointer
/// field count, so field counts are exact; scalar areas may be padded
/// (layout reference), so those are minimum checks at use sites.
pub(crate) fn ctor<'r>(
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

pub(crate) fn boolean(byte: Option<&u8>, expected: &'static str) -> Result<bool, OleanError> {
    match byte.copied() {
        Some(0) => Ok(false),
        Some(1) => Ok(true),
        _ => Err(bad(expected)),
    }
}

pub(crate) fn nat(r: &Raw) -> Result<Nat, OleanError> {
    match &**r {
        RawValue::Scalar(v) => Ok(Nat::from(*v)),
        RawValue::BigInt(i) => {
            let mag: BigUint = i.clone().try_into().map_err(|_| bad("non-negative Nat"))?;
            Ok(Nat(mag))
        }
        _ => Err(bad("Nat")),
    }
}

pub(crate) fn int(r: &Raw) -> Result<Int, OleanError> {
    match &**r {
        // Boxed Int scalars are 63-bit two's complement (lean.h
        // lean_scalar_to_int): sign-extend from bit 62.
        RawValue::Scalar(v) => Ok(Int(BigInt::from(((v << 1) as i64) >> 1))),
        RawValue::BigInt(i) => Ok(Int(i.clone())),
        _ => Err(bad("Int")),
    }
}

pub(crate) fn string(r: &Raw) -> Result<String, OleanError> {
    match &**r {
        RawValue::Str(s) => Ok(s.clone()),
        _ => Err(bad("String")),
    }
}

/// `List α` → element raw nodes (nil = box(0), cons = tag 1).
pub(crate) fn list(r: &Raw) -> Result<Vec<&Raw>, OleanError> {
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

pub(crate) fn array(r: &Raw) -> Result<&[Raw], OleanError> {
    match &**r {
        RawValue::Array(elems) => Ok(elems),
        _ => Err(bad("Array")),
    }
}

/// `Substring.Raw` (Init/Prelude.lean:3582): tag 0, 3 obj fields
/// (`str`, `startPos`, `stopPos`). `startPos`/`stopPos` are
/// `String.Pos.Raw` (Init/Prelude.lean:3557), a single-field struct
/// over `byteIdx : Nat`, so each decodes directly as a `Nat`.
fn substring(r: &Raw) -> Result<Substring, OleanError> {
    let (fields, _) = ctor(r, 0, 3, "Substring")?;
    Ok(Substring {
        str: string(&fields[0])?,
        start_pos: nat(&fields[1])?,
        stop_pos: nat(&fields[2])?,
    })
}

/// `SourceInfo` (Init/Prelude.lean:4827): `original` (tag 0, 4 obj
/// fields), `synthetic` (tag 1, 2 obj fields + `canonical : Bool` u8 at
/// scalar offset 0), `none` (fieldless → `box(2)`).
pub(crate) fn source_info(r: &Raw) -> Result<SourceInfo, OleanError> {
    match &**r {
        RawValue::Scalar(2) => Ok(SourceInfo::None),
        RawValue::Ctor { tag: 0, fields, .. } if fields.len() == 4 => Ok(SourceInfo::Original {
            leading: substring(&fields[0])?,
            pos: nat(&fields[1])?,
            trailing: substring(&fields[2])?,
            end_pos: nat(&fields[3])?,
        }),
        RawValue::Ctor {
            tag: 1,
            fields,
            scalars,
        } if fields.len() == 2 => Ok(SourceInfo::Synthetic {
            pos: nat(&fields[0])?,
            end_pos: nat(&fields[1])?,
            canonical: boolean(scalars.first(), "SourceInfo.canonical")?,
        }),
        _ => Err(bad("SourceInfo")),
    }
}

/// ReducibilityHints (Declaration.lean:46-50). Representation-agnostic
/// (returns a plain enum) — shared by every `ConstantInfo`
/// representation (`interp_id.rs`'s id-native decode, and this crate's
/// callers generally).
pub(crate) fn reducibility(r: &Raw) -> Result<ReducibilityHints, OleanError> {
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

pub(crate) struct Interp {
    names: HashMap<*const RawValue, Arc<Name>>,
    syntaxes: HashMap<*const RawValue, Arc<Syntax>>,
    anonymous: Arc<Name>,
    missing: Arc<Syntax>,
}

impl Interp {
    pub(crate) fn new() -> Interp {
        Interp {
            names: HashMap::new(),
            syntaxes: HashMap::new(),
            anonymous: Arc::new(Name::Anonymous),
            missing: Arc::new(Syntax::Missing),
        }
    }

    /// Name (Init/Prelude.lean:4693-4717): walk the parent chain down
    /// iteratively, then build back up, memoizing each node.
    pub(crate) fn name(&mut self, r: &Raw) -> Result<Arc<Name>, OleanError> {
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

    fn sub_syntax(&self, r: &Raw) -> Result<Arc<Syntax>, OleanError> {
        if let RawValue::Scalar(0) = &**r {
            return Ok(Arc::clone(&self.missing));
        }
        self.syntaxes
            .get(&key(r))
            .cloned()
            .ok_or_else(|| bad("Syntax subterm"))
    }

    /// `Syntax` (Init/Prelude.lean:4943): explicit-stack post-order walk
    /// because node depth (`Node.args`) is attacker-controlled.
    /// `missing` = `box(0)`; `node` (tag 1, 3 obj fields), `atom`
    /// (tag 2, 2 obj fields), `ident` (tag 3, 4 obj fields). Only
    /// `node.args` recurse into `Syntax`; the rest are leaves.
    pub(crate) fn syntax(&mut self, root: &Raw) -> Result<Arc<Syntax>, OleanError> {
        enum Step<'r> {
            Visit(&'r Raw),
            Build(&'r Raw),
        }
        let mut stack = vec![Step::Visit(root)];
        while let Some(step) = stack.pop() {
            match step {
                Step::Visit(r) => {
                    if matches!(&**r, RawValue::Scalar(0)) || self.syntaxes.contains_key(&key(r)) {
                        continue;
                    }
                    match &**r {
                        RawValue::Ctor { tag: 1, fields, .. } if fields.len() == 3 => {
                            stack.push(Step::Build(r));
                            for child in array(&fields[2])? {
                                stack.push(Step::Visit(child));
                            }
                        }
                        RawValue::Ctor { tag: 2, fields, .. } if fields.len() == 2 => {
                            stack.push(Step::Build(r));
                        }
                        RawValue::Ctor { tag: 3, fields, .. } if fields.len() == 4 => {
                            stack.push(Step::Build(r));
                        }
                        _ => return Err(bad("Syntax")),
                    }
                }
                Step::Build(r) => {
                    let s = self.build_syntax(r)?;
                    self.syntaxes.insert(key(r), s);
                }
            }
        }
        self.sub_syntax(root)
    }

    fn build_syntax(&mut self, r: &Raw) -> Result<Arc<Syntax>, OleanError> {
        let syntax = match &**r {
            RawValue::Ctor { tag: 1, fields, .. } if fields.len() == 3 => Syntax::Node {
                info: source_info(&fields[0])?,
                kind: self.name(&fields[1])?,
                args: array(&fields[2])?
                    .iter()
                    .map(|a| self.sub_syntax(a))
                    .collect::<Result<_, _>>()?,
            },
            RawValue::Ctor { tag: 2, fields, .. } if fields.len() == 2 => Syntax::Atom {
                info: source_info(&fields[0])?,
                val: string(&fields[1])?,
            },
            RawValue::Ctor { tag: 3, fields, .. } if fields.len() == 4 => Syntax::Ident {
                info: source_info(&fields[0])?,
                raw_val: substring(&fields[1])?,
                val: self.name(&fields[2])?,
                preresolved: list(&fields[3])?
                    .into_iter()
                    .map(|p| self.preresolved(p))
                    .collect::<Result<_, _>>()?,
            },
            _ => unreachable!("shape checked in Visit"),
        };
        Ok(Arc::new(syntax))
    }

    /// `Syntax.Preresolved` (Init/Prelude.lean:4930): `namespace`
    /// (tag 0, 1 obj field), `decl` (tag 1, 2 obj fields).
    fn preresolved(&mut self, r: &Raw) -> Result<Preresolved, OleanError> {
        match &**r {
            RawValue::Ctor { tag: 0, fields, .. } if fields.len() == 1 => {
                Ok(Preresolved::Namespace(self.name(&fields[0])?))
            }
            RawValue::Ctor { tag: 1, fields, .. } if fields.len() == 2 => Ok(Preresolved::Decl {
                name: self.name(&fields[0])?,
                fields: list(&fields[1])?
                    .into_iter()
                    .map(string)
                    .collect::<Result<_, _>>()?,
            }),
            _ => Err(bad("Preresolved")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ctor_raw(tag: u8, fields: Vec<Raw>, scalars: Vec<u8>) -> Raw {
        Arc::new(RawValue::Ctor {
            tag,
            fields,
            scalars,
        })
    }

    fn scalar(v: u64) -> Raw {
        Arc::new(RawValue::Scalar(v))
    }

    fn str_raw(s: &str) -> Raw {
        Arc::new(RawValue::Str(s.to_string()))
    }

    // List cons/nil (nil = box(0), cons = tag 1, 2 fields).
    fn cons(head: Raw, tail: Raw) -> Raw {
        ctor_raw(1, vec![head, tail], vec![])
    }

    // Substring.Raw: tag 0, 3 obj fields.
    fn substring_raw() -> Raw {
        ctor_raw(0, vec![str_raw("x"), scalar(0), scalar(1)], vec![])
    }

    #[test]
    fn decodes_ident_with_preresolved_list() {
        // preresolved = [namespace(anon), decl(anon, ["f"])]
        let ns = ctor_raw(0, vec![scalar(0)], vec![]);
        let decl = ctor_raw(1, vec![scalar(0), cons(str_raw("f"), scalar(0))], vec![]);
        let preresolved = cons(ns, cons(decl, scalar(0)));
        // ident: tag 3, 4 obj fields (info=none, rawVal, val=anon, preresolved)
        let ident = ctor_raw(
            3,
            vec![scalar(2), substring_raw(), scalar(0), preresolved],
            vec![],
        );
        let mut interp = Interp::new();
        let s = interp.syntax(&ident).expect("ident decodes");
        match &*s {
            Syntax::Ident {
                info: SourceInfo::None,
                raw_val,
                preresolved,
                ..
            } => {
                assert_eq!(raw_val.str, "x");
                assert_eq!(preresolved.len(), 2);
                assert!(matches!(preresolved[0], Preresolved::Namespace(_)));
                match &preresolved[1] {
                    Preresolved::Decl { fields, .. } => assert_eq!(fields, &["f".to_string()]),
                    _ => panic!("expected decl"),
                }
            }
            _ => panic!("expected ident"),
        }
    }

    #[test]
    fn shared_arg_child_decodes_to_one_shared_arc() {
        // A node with two arg slots pointing at the SAME raw atom node:
        // sharing must be preserved (one raw node → one Arc).
        let atom = ctor_raw(2, vec![scalar(2), str_raw("+")], vec![]);
        let args = Arc::new(RawValue::Array(vec![Arc::clone(&atom), Arc::clone(&atom)]));
        let node = ctor_raw(1, vec![scalar(2), scalar(0), args], vec![]);
        let mut interp = Interp::new();
        let s = interp.syntax(&node).expect("node decodes");
        match &*s {
            Syntax::Node { args, .. } => {
                assert_eq!(args.len(), 2);
                assert!(Arc::ptr_eq(&args[0], &args[1]), "sharing not preserved");
            }
            _ => panic!("expected node"),
        }
    }

    #[test]
    fn synthetic_source_info_bad_canonical_byte_is_bad_shape() {
        // synthetic: tag 1, 2 obj fields, canonical u8 at scalar 0.
        // Byte 2 is neither false(0) nor true(1) → BadShape via boolean.
        let synthetic = ctor_raw(1, vec![scalar(0), scalar(0)], vec![2]);
        let err = source_info(&synthetic).expect_err("bad canonical byte");
        assert!(matches!(err, OleanError::BadShape { .. }));
    }

    #[test]
    fn wrong_field_count_node_is_bad_shape() {
        // node requires 3 obj fields; give 2.
        let node = ctor_raw(1, vec![scalar(2), scalar(0)], vec![]);
        let mut interp = Interp::new();
        let err = interp.syntax(&node).expect_err("wrong field count");
        assert!(matches!(err, OleanError::BadShape { .. }));
    }
}
