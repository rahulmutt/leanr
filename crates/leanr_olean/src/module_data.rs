//! The decoded contents of one `.olean` module (oracle:
//! src/Lean/Environment.lean:109-129).

use std::sync::Arc;

use leanr_kernel::bank::{NameId, Store};
use leanr_kernel::{ConstantInfo, Name, Nat};

use crate::interp_id::InterpId;
use crate::{raw, OleanError};

/// oracle: src/Lean/Setup.lean:25-32
#[derive(Debug, Clone)]
pub struct Import {
    pub module: Arc<Name>,
    pub import_all: bool,
    pub is_exported: bool,
    pub is_meta: bool,
}

/// Which companion part a byte buffer is, for [`ModuleData::parse_parts`].
///
/// The module system (pinned toolchain v4.32.0-rc1) can split one module
/// into a base `Foo.olean` plus `Foo.olean.server` and `Foo.olean.private`
/// companion parts (oracle: `OLeanLevel.adjustFileName`,
/// src/Lean/Environment.lean:1793-1796). The base part alone is a
/// self-contained region and carries the module's public constant subset;
/// the `.private` part carries the module's *full* constant set (oracle:
/// `mkModuleData`, Environment.lean:1843-1852 — the `.private` level folds
/// in every kernel constant, while lower levels are filtered to the exported
/// subset), stored with objects deduplicated against the earlier parts.
///
/// The kind is used only to pick the primary part (the base) for the
/// module's non-constant fields; pointer resolution is by logical address
/// range and does not depend on it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PartKind {
    /// The base `Foo.olean` (public/exported level).
    Base,
    /// The `Foo.olean.server` part (language-server extension state).
    Server,
    /// The `Foo.olean.private` part (full constant set).
    Private,
}

/// `LeadingIdentBehavior` (oracle: Parser/Basic.lean:1643-1659); tag order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CatBehavior {
    Default,
    Symbol,
    Both,
}

/// One typed `Lean.Parser.parserExtension` olean entry
/// (oracle `ParserExtension.OLeanEntry`, Parser/Extension.lean:57-62;
/// tag order). `prio` is dropped: no leanr consumer reads it (dispatch
/// is longest-match) — see the M3b2a design spec.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParserEntry {
    Token(String),
    Kind(NameId),
    Category {
        cat: NameId,
        decl: NameId,
        behavior: CatBehavior,
    },
    Parser {
        cat: NameId,
        decl: NameId,
    },
}

/// Scope wrapper (oracle `ScopedEnvExtension.Entry`): `local` never
/// serializes; `scoped` carries its activation namespace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EntryScope {
    Global,
    Scoped(NameId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScopedParserEntry {
    pub scope: EntryScope,
    pub entry: ParserEntry,
}

/// oracle: `ReducibilityStatus` (ReducibilityAttrs.lean:40-42). All
/// constructors are nullary, so DECLARATION order is ctor-tag order:
/// reducible=0, semireducible=1, irreducible=2, implicitReducible=3,
/// instanceReducible=4.
///
/// Tag order is deliberately NOT unfolding order — the in-source comment
/// records that the last two were appended out of semantic order for
/// bootstrapping. Consumers must not derive an ordering from this enum's
/// declaration order; see `leanr_meta::transparency`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReducibilityStatus {
    Reducible,
    Semireducible,
    Irreducible,
    ImplicitReducible,
    InstanceReducible,
}

/// One decoded reducibility-attribute entry, from either
/// `reducibilityCore` (always `Global`, unwrapped) or
/// `reducibilityExtra` (wrapped in `ScopedEnvExtension.Entry`).
///
/// A constant with no entry has status `Semireducible`
/// (`getReducibilityStatusCore`'s fallback, ReducibilityAttrs.lean:79-88).
#[derive(Debug, Clone)]
pub struct ReducibilityEntry {
    pub scope: EntryScope,
    pub name: NameId,
    pub status: ReducibilityStatus,
}

/// oracle: `Lean.Meta.Match.AltParamInfo` (MatcherInfo.lean:38-45).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatcherAltInfo {
    pub num_fields: Nat,
    pub num_overlaps: Nat,
    pub has_unit_thunk: bool,
}

/// oracle: `Lean.Meta.DiscrTree.Key`
/// (Meta/DiscrTree/Types.lean:16-24, pinned toolchain v4.33.0-rc1):
///
/// ```text
/// inductive Key where
///   | star  : Key                     -- 0, nullary
///   | other : Key                     -- 1, nullary
///   | lit   : Literal → Key           -- 2
///   | fvar  : FVarId → Nat → Key      -- 3
///   | const : Name → Nat → Key        -- 4
///   | arrow : Key                     -- 5, nullary
///   | proj  : Name → Nat → Nat → Key  -- 6
/// ```
///
/// CONFIRMED against the source above: this is a 7-ctor inductive, NOT
/// the 9-variant Const/Fvar/Bvar/Lit/Star/Other/Arrow/Proj/Sort shape a
/// prior draft of this plan expected. There is no `Bvar` and no `Sort`
/// constructor on `Key` — a bound variable's *type* is what gets
/// indexed (never the de Bruijn variable itself, which cannot recur
/// across unifiable instances), and `Sort` is deliberately folded into
/// `other`/`star` by `DiscrTree.Main`'s key-pushing logic rather than
/// carried as its own `Key` case. The source wins over the brief's
/// schematic; ctor tags below are the declaration-order indices shown
/// above, following the same convention already pinned by `Level` and
/// `Option` in this crate (nullary ctors are boxed scalar immediates —
/// `RawValue::Scalar(tag)` — at their plain declaration index; this is
/// not something `DiscrKey` introduces, see `interp_id.rs::level`/
/// `opt_nat`'s doc comments for the two prior confirmations of the
/// rule). `fvar`'s `FVarId` field is decoded only for shape (an
/// `FVarId` is a single-field `{ name : Name }` structure, unboxed to
/// its one field on the wire — same reasoning as `matcher_entry`'s
/// `DiscrInfo` note) and then discarded: fvar identity is not stable
/// across serialization, so only `arity` is kept (field-order pinned
/// against `DiscrTree/Main.lean:299-301`'s `.fvar fvarId nargs`).
/// `proj`'s three fields are `structure`, `index`, `arity` in that
/// order (`DiscrTree/Main.lean:291-300`'s `.proj s i nargs`). `Lit`
/// reuses `leanr_kernel::Literal`, the same type `interp_id.rs`
/// already builds for `Expr.lit` (see `build_expr`'s tag-9 arm) —
/// no new literal type is introduced.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DiscrKey {
    Star,
    Other,
    Lit(leanr_kernel::Literal),
    /// `fvar` identity is not serialized stably; only arity survives.
    Fvar { arity: usize },
    Const { name: NameId, arity: usize },
    Arrow,
    Proj {
        structure: NameId,
        index: usize,
        arity: usize,
    },
}

/// One decoded matcher-extension entry: oracle
/// `Lean.Meta.Match.Extension.Entry` = `{ name, info : MatcherInfo }`
/// (MatcherInfo.lean:113-115, 52-68). v4.33 stores `altInfos`
/// (per-alternative field/overlap/thunk counts), NOT the older
/// `altNumParams`; the consumer derives per-alt arity
/// (`MatcherInfo.altNumParams`, MatcherInfo.lean:106-108).
///
/// `MatcherInfo` itself has a 6th field, `overlaps : Overlaps`
/// (MatcherInfo.lean:64), not mentioned by the task-1 brief's 5-field
/// schematic — verified against the real oracle source and confirmed
/// empirically (the decoded ctor has 6 pointer fields). `overlaps` is
/// validated only by the outer ctor's exact field-count check and is
/// never read: no leanr consumer needs the overlap-approximation data,
/// only `reduce_matcher`'s saturation/alternative-selection inputs.
#[derive(Debug, Clone)]
pub struct MatcherEntry {
    pub name: NameId,
    pub num_params: Nat,
    pub num_discrs: Nat,
    pub alt_infos: Vec<MatcherAltInfo>,
    /// `uElimPos?` — `some pos` when the matcher eliminates into
    /// polymorphic universes.
    pub u_elim_pos: Option<Nat>,
    /// `discrInfos[i].hName?` — the `h :` annotation name per
    /// discriminant, flattened (DiscrInfo has exactly one field, and
    /// the oracle's single-field-structure runtime representation
    /// stores it unwrapped — see `interp_id.rs::matcher_entry`'s doc).
    pub discr_infos: Vec<Option<NameId>>,
}

/// The decoded contents of one `.olean` module, decoded directly into
/// term-bank ids (term-bank phase 3 — the Arc decode path this used to
/// have a twin of is deleted, along with the differential gate that
/// checked the two agreed id-for-id; see `interp.rs`'s module doc).
/// Ids live in the `&mut Store` handed to `parse`/`parse_parts` — the
/// caller's `Environment::store_mut()` in the check pipeline, or a
/// standalone `Store::persistent()` for inspection commands.
#[derive(Debug)]
pub struct ModuleData {
    pub is_module: bool,
    pub imports: Vec<Import>,
    pub const_names: Vec<NameId>,
    pub constants: Vec<ConstantInfo>,
    pub extra_const_names: Vec<NameId>,
    /// Environment-extension entries are validated by phase A but kept
    /// opaque (spec: interpreted by the elaborator in M4).
    pub num_entries: usize,
    /// Typed decode of the `Lean.Parser.parserExtension` entries pair
    /// (M3b2a); all other extension entries stay opaque (folded into
    /// `num_entries` only).
    pub parser_entries: Vec<ScopedParserEntry>,
    /// Typed decode of the `reducibilityCore` / `reducibilityExtra`
    /// extension entries (M4a). All other extension entries stay opaque
    /// (folded into `num_entries` only).
    pub reducibility: Vec<ReducibilityEntry>,
    /// Typed decode of the `Lean.Meta.Match.Extension.extension`
    /// entries (M4a plan 2). All other extension entries stay opaque.
    pub matchers: Vec<MatcherEntry>,
}

impl ModuleData {
    /// Decode a whole single-region `.olean` file directly into `st`.
    /// `bytes` is untrusted input; every failure mode is an
    /// `OleanError`, never a panic. A failed decode may leave
    /// already-interned rows in `st` — sound (interning is append-only
    /// and canonical; unreachable ids are inert) and decode failure is
    /// fatal for the run.
    ///
    /// This is the M1a single-file path and is unchanged: byte-for-byte the
    /// same as decoding one part with [`ModuleData::parse_parts`].
    pub fn parse(bytes: &[u8], st: &mut Store) -> Result<ModuleData, OleanError> {
        let root = raw::parse_bytes(bytes)?;
        InterpId::new(st).module_data(&root)
    }

    /// Decode a module split across its ordered companion parts, producing
    /// the module's FULL constant set (base plus `.olean.server`/
    /// `.olean.private`).
    ///
    /// All parts are mapped into one logical address space so a companion
    /// part's pointers into an earlier part's deduplicated objects resolve
    /// (oracle: `readModuleDataParts`, Environment.lean:1755-1763, reads each
    /// part against the accumulated regions of the prior parts). The parts
    /// should be given base-first, matching the oracle's load order
    /// (`readModuleDataPartsOfMod`, Environment.lean:2042-2055 loads
    /// `[base, server, private]`), though resolution itself is order-free.
    ///
    /// Constants from every part are merged into one constant map, preferring
    /// the most authoritative part (`.private` > `.server` > base) for each
    /// name. Rationale: the oracle picks ONE part per module for the kernel
    /// constant map — `mainModule?` (Environment.lean:1999-2003) is
    /// `getData? (if self.importAll then .private else .exported)`, so an
    /// `import all` consumer gets the `.private` part (the full, checkable
    /// constant set) while a plain importer deliberately gets the base
    /// (`.exported`) interface. The base part stores only that public
    /// *interface*: a public `def`/`theorem` whose body is not exposed is
    /// written as a bare **axiom** stub there (verified on the pinned
    /// toolchain — `bump`/`triv` are `axiom` in `ModPriv.olean` but the real
    /// `def`/`thm` in `ModPriv.olean.private`). leanr's consumer is a full
    /// fresh-check (replay needs checkable bodies), i.e. the `importAll`
    /// semantics, so `.private` wins here.
    ///
    /// A name therefore legitimately appears in several parts with DIFFERENT
    /// infos (axiom stub vs. full def). Note the oracle never *reconciles*
    /// such cross-part pairs — `mainModule?` picks exactly one part, so a
    /// module's parts never meet in its constant map (its `subsumesInfo`,
    /// Environment.lean:2209-2225, reconciles cross-MODULE duplicates only,
    /// and its arms would reject a def/axiom pair via `| _, _ => false`).
    /// The shadowed-duplicate guard below is therefore leanr's own
    /// conservative check, consistent with the oracle's one-part-per-module
    /// model: a shadowed duplicate must share `type` and `levelParams` with
    /// the kept version (the invariant every `subsumesInfo` arm also
    /// requires); a disagreement is real corruption and a decode error.
    ///
    /// The module's non-constant fields (`is_module`, `imports`,
    /// `num_entries`) are taken from the base part. Requires exactly one
    /// [`PartKind::Base`] part.
    pub fn parse_parts(
        parts: &[(PartKind, &[u8])],
        st: &mut Store,
    ) -> Result<ModuleData, OleanError> {
        let base_positions: Vec<usize> = parts
            .iter()
            .enumerate()
            .filter(|(_, (k, _))| *k == PartKind::Base)
            .map(|(i, _)| i)
            .collect();
        let [base_idx] = base_positions[..] else {
            return Err(OleanError::BadShape {
                expected: "exactly one Base part in parse_parts",
            });
        };

        let byte_slices: Vec<&[u8]> = parts.iter().map(|(_, b)| *b).collect();
        let roots = raw::parse_parts_bytes(&byte_slices)?;

        // One shared interpreter: objects shared across parts decode to
        // the same id (memos keyed by raw node address). The block
        // scopes the &mut Store borrow so `st` is usable for error
        // rendering below.
        let mut modules: Vec<ModuleData> = {
            let mut interp = InterpId::new(st);
            roots
                .iter()
                .map(|r| interp.module_data(r))
                .collect::<Result<_, _>>()?
        };

        // Most-authoritative first: `.private` > `.server` > base.
        let authority = |k: PartKind| match k {
            PartKind::Private => 0,
            PartKind::Server => 1,
            PartKind::Base => 2,
        };
        let mut order: Vec<usize> = (0..modules.len()).collect();
        order.sort_by_key(|&i| authority(parts[i].0));

        let mut const_names: Vec<NameId> = Vec::new();
        let mut constants: Vec<ConstantInfo> = Vec::new();
        let mut seen: std::collections::HashMap<NameId, usize> = std::collections::HashMap::new();
        for &i in &order {
            for c in &modules[i].constants {
                let name = c.name();
                match seen.get(&name) {
                    None => {
                        seen.insert(name, constants.len());
                        const_names.push(name);
                        constants.push(c.clone());
                    }
                    Some(&existing) => {
                        // Shadowed duplicate must share `type` +
                        // `levelParams` with the kept version. By the
                        // interning invariant id equality IS the Arc
                        // version's guarded structural_eq, so this is
                        // plain `==` — no RecGuard, no DeepRecursion.
                        let kept = constants[existing].constant_val();
                        let dup = c.constant_val();
                        let compatible = kept.level_params == dup.level_params && kept.ty == dup.ty;
                        if !compatible {
                            return Err(OleanError::DuplicateConstant {
                                name: st.to_name(None, Some(name)).to_string(),
                            });
                        }
                    }
                }
            }
        }

        // Extra const names: union preserving first-seen order.
        let mut extra_seen: std::collections::HashSet<NameId> = std::collections::HashSet::new();
        let mut extra_const_names: Vec<NameId> = Vec::new();
        for &i in &order {
            for &n in &modules[i].extra_const_names {
                if extra_seen.insert(n) {
                    extra_const_names.push(n);
                }
            }
        }

        let base = &mut modules[base_idx];
        Ok(ModuleData {
            is_module: base.is_module,
            imports: std::mem::take(&mut base.imports),
            const_names,
            constants,
            extra_const_names,
            num_entries: base.num_entries,
            parser_entries: std::mem::take(&mut base.parser_entries),
            reducibility: std::mem::take(&mut base.reducibility),
            matchers: std::mem::take(&mut base.matchers),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use leanr_kernel::bank::NameId;
    use leanr_kernel::{ConstantInfo, Environment};
    use std::collections::HashMap;
    use std::path::PathBuf;

    fn fixture(name: &str) -> Vec<u8> {
        std::fs::read(
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../../tests/fixtures")
                .join(name),
        )
        .unwrap()
    }

    /// Id-path mirror of `check_fixtures.rs`'s
    /// `modpriv_parts_replay_from_empty_env`: multi-region merge on the
    /// id path — `.private` wins over the base axiom stub, the private
    /// helper is present, and the merged set replays clean.
    #[test]
    fn modpriv_parts_id_decode_and_replay() {
        let base = fixture("ModPriv.olean");
        let server = fixture("ModPriv.olean.server");
        let private = fixture("ModPriv.olean.private");

        let mut env = Environment::default();
        let md = ModuleData::parse_parts(
            &[
                (PartKind::Base, &base),
                (PartKind::Server, &server),
                (PartKind::Private, &private),
            ],
            env.store_mut(),
        )
        .expect("parts decode");
        assert!(md.is_module);
        assert!(md.imports.is_empty());

        let render = |env: &Environment, n: NameId| env.store().to_name(None, Some(n)).to_string();
        assert!(
            md.constants
                .iter()
                .any(|c| render(&env, c.name()) == "_private.ModPriv.0.secret"),
            "private helper missing from merged constants"
        );
        let bump = md
            .constants
            .iter()
            .find(|c| render(&env, c.name()) == "bump")
            .expect("bump present");
        assert_eq!(
            bump.kind(),
            "def",
            "bump must be the private def, not an axiom stub"
        );

        let constants: HashMap<NameId, ConstantInfo> =
            md.constants.into_iter().map(|c| (c.name(), c)).collect();
        let stats = leanr_kernel::replay(&mut env, constants).expect("replays clean");
        assert!(
            stats.checked >= 5,
            "expected >= 5 checked, got {}",
            stats.checked
        );
        assert_eq!(stats.skipped_unsafe, 0);
    }

    /// The reducibility extensions decode, and a constant with no
    /// attribute is ABSENT (its status is the `.semireducible` default,
    /// not a stored entry).
    #[test]
    fn reducibility_entries_decode() {
        use crate::{EntryScope, ReducibilityStatus};

        let bytes = fixture("Reducibility.olean");
        let mut env = Environment::default();
        let md = ModuleData::parse(&bytes, env.store_mut()).expect("decode");

        let render = |env: &Environment, n: NameId| env.store().to_name(None, Some(n)).to_string();
        let got: Vec<(String, ReducibilityStatus)> = md
            .reducibility
            .iter()
            .map(|e| (render(&env, e.name), e.status))
            .collect();

        for (name, want) in [
            ("redDef", ReducibilityStatus::Reducible),
            ("irredDef", ReducibilityStatus::Irreducible),
            ("instRedDef", ReducibilityStatus::InstanceReducible),
            ("implRedDef", ReducibilityStatus::ImplicitReducible),
        ] {
            assert!(
                got.contains(&(name.to_string(), want)),
                "missing {name} => {want:?}; got {got:?}"
            );
        }

        assert!(
            !got.iter().any(|(n, _)| n == "plainDef"),
            "plainDef carries no attribute so it must not appear: {got:?}"
        );

        // reducibilityCore is unwrapped, so every entry from it is Global.
        assert!(md
            .reducibility
            .iter()
            .all(|e| matches!(e.scope, EntryScope::Global)));
    }

    /// `reducibilityCore`'s array is sorted by `Name.quickLt` and
    /// `getReducibilityStatusCore` binary-searches it. We do not depend
    /// on the ordering, but a violation means the shape assumption is
    /// wrong, so assert the array is non-empty and every entry resolved.
    #[test]
    fn reducibility_entries_are_nonempty() {
        let bytes = fixture("Reducibility.olean");
        let mut env = Environment::default();
        let md = ModuleData::parse(&bytes, env.store_mut()).expect("decode");
        assert!(!md.reducibility.is_empty());
    }

    /// The matcher extension decodes: every `match` in Matcher.lean
    /// registered one entry; `plainId` (no match) contributed none.
    #[test]
    fn matcher_entries_decode() {
        let bytes = fixture("Matcher.olean");
        let mut env = Environment::default();
        let md = ModuleData::parse(&bytes, env.store_mut()).expect("decode");

        assert!(
            md.matchers.len() >= 2,
            "isZero and both must each register a matcher: {:?}",
            md.matchers.len()
        );

        let render = |n| env.store().to_name(None, Some(n)).to_string();
        // Matcher aux names are `<decl>.match_<i>`-shaped.
        assert!(
            md.matchers
                .iter()
                .any(|m| render(m.name).contains("match_")),
            "expected match_ aux names"
        );
        for m in &md.matchers {
            // Every matcher in this fixture has 2 alternatives, and
            // discrInfos has one entry per discriminant.
            assert_eq!(
                m.alt_infos.len(),
                2,
                "unexpected alt count: {:?}",
                render(m.name)
            );
            assert_eq!(
                leanr_kernel::Nat::from(m.discr_infos.len() as u64),
                m.num_discrs,
                "discrInfos length must equal numDiscrs: {:?}",
                render(m.name)
            );
        }
        // `isZero` has 1 discriminant, `both` has 2.
        assert!(md
            .matchers
            .iter()
            .any(|m| m.num_discrs == leanr_kernel::Nat::from(1u64)));
        assert!(md
            .matchers
            .iter()
            .any(|m| m.num_discrs == leanr_kernel::Nat::from(2u64)));
    }

    /// Task 7: `count` (Matcher.lean) is structurally recursive, so the
    /// equation compiler emits a `count._sunfold` auxiliary alongside it
    /// (`mkSmartUnfoldingNameFor`, WHNF.lean:50-51) — a plain constant
    /// in `const_names`, no separate extension involved. Probe-free:
    /// this only needs `ModuleData.const_names` and `Store::to_name`.
    #[test]
    fn count_sunfold_decodes() {
        let bytes = fixture("Matcher.olean");
        let mut env = Environment::default();
        let md = ModuleData::parse(&bytes, env.store_mut()).expect("decode");

        let render = |n: NameId| env.store().to_name(None, Some(n)).to_string();
        assert!(
            md.const_names.iter().any(|&n| render(n) == "count"),
            "count itself must be declared"
        );
        assert!(
            md.const_names
                .iter()
                .any(|&n| render(n) == "count._sunfold"),
            "structural recursion must emit a count._sunfold auxiliary: {:?}",
            md.const_names
                .iter()
                .map(|&n| render(n))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn parse_parts_requires_exactly_one_base() {
        let base = fixture("ModPriv.olean");
        let mut env = Environment::default();
        let err = ModuleData::parse_parts(&[(PartKind::Private, &base)], env.store_mut())
            .expect_err("no base part");
        assert!(matches!(err, OleanError::BadShape { .. }));
    }
}
