//! Query-side discrimination-path computation: `MetaCtx::mk_path` and
//! `MetaCtx::discr_get_match`.
//!
//! oracle: `Lean.Meta.DiscrTree.mkPath`/`mkPathAux`/`pushArgs`
//! (`Lean/Meta/DiscrTree/Main.lean`, toolchain leanprover/lean4:
//! v4.33.0-rc1). Every rule below cites the exact line range read from
//! that file.
//!
//! # Insert-side vs. query-side (read this before touching `ignoreArg`)
//!
//! The oracle has TWO distinct key-computation families, and B1
//! (`discr_tree.rs`) already flags which one it transcribes:
//!
//! - `mkPath`/`mkPathAux`/`pushArgs` (Main.lean:114-153): used when
//!   REGISTERING a value in a `DiscrTree` (`DiscrTree.insert`,
//!   Main.lean:155-158). This is the one that calls `ignoreArg`
//!   (Main.lean:105-115): instance-implicit and non-type-implicit/proof
//!   ARGUMENTS are replaced by a `Star` placeholder before recursion, so
//!   they occupy exactly one flattened path slot and are never
//!   structurally indexed.
//! - `getKeyArgs`/`getUnifyKeyArgs` (Main.lean:349-413, `isMatch :=
//!   false`): used by `getUnify` (Main.lean:565-590), the function B1
//!   transcribes. Its `.const`/`.fvar`/`.proj` arms return `e.
//!   getAppRevArgs` UNFILTERED — no `ignoreArg` call anywhere in this
//!   family.
//!
//! For THIS plan, `mkPath`'s own transcription target is irrelevant to
//! how instances get their stored keys: per `discr_tree.rs`'s own module
//! doc, `InstanceEntry.keys` are decoded DIRECTLY off `.olean` bytes
//! (PR-A) — the toolchain itself already ran `mkPath` at compile time
//! and serialized the result; B3 never calls this module's `mk_path` to
//! build a stored path. `mk_path`/`discr_get_match` here are therefore
//! QUERY-side only: computing the flattened path for a synthesis GOAL
//! (`SynthInstance.lean:210-211`'s `globalInstances.getUnify type`) to
//! feed `DiscrTree::get_match_keys` (B1's `getUnify.process`
//! transcription).
//!
//! Given that, the "faithful" pairing for B1 would be
//! `getUnify`'s own unfiltered `getUnifyKeyArgs`, not `ignoreArg`-
//! filtering `pushArgs`. This module implements `pushArgs`/`ignoreArg`
//! filtering ANYWAY, for three reasons, checked against B1's own
//! `process`/`visitStar` semantics (`discr_tree.rs:230-255`):
//!
//! 1. It's what this task's brief explicitly asks for and tests
//!    ("risk 6") — `mk_path` (named after `mkPath`, not
//!    `getUnifyKeyArgs`) is meant to be reusable for OTHER discrimination-
//!    tree consumers this crate will grow later (`discr_tree.rs`'s own
//!    doc: "simp/rw slices reuse this module later"), where insertion
//!    genuinely needs `ignoreArg`.
//! 2. Filtering here is SUPERSET-SAFE for `get_match_keys`'s purposes,
//!    at every position, not just the ones `ignoreArg` fires on (this is
//!    the reviewer's simpler, actually-valid argument — a prior draft of
//!    this doc argued "the insert side ALWAYS stores `Star` there too",
//!    which is not strictly true: insert-side `ignoreArg`'s own
//!    `Implicit ⇒ !isType a` verdict depends on the STORED argument,
//!    which can differ from what the query happens to pass at the same
//!    position, so the two sides are not guaranteed to agree on
//!    `Star`-vs-real independently of this argument). The real
//!    invariant is about `findKey`/`process` (`discr_tree.rs`'s own
//!    transcription), not about the two sides agreeing: for ANY
//!    position, a `Star` QUERY key visits every child of the current
//!    trie node with `skip = key_arity(child)`, resuming the SAME
//!    continuation regardless of which child that is (Main.lean:
//!    594-599's `visitStar`; `discr_tree.rs`'s `skip_args`) — i.e. it
//!    is the query-side equivalent of "match anything here, then keep
//!    going". Replacing a real subterm's key with `Star` in the query
//!    path therefore visits a SUPERSET of what querying the real key
//!    would visit at that node: `results(Star-at-position) ⊇
//!    results(real-key-at-position)`, pointwise over every stored entry.
//!    Filtering here can only ADD candidates B1's own `is_def_eq` will
//!    later re-check and reject, never DROP one that a real match
//!    should have found.
//! 3. For THIS plan's actual synthesis goals (`Add N`, `Add (Prod a
//!    b)`, ...) `ignoreArg` never fires at all: `getInstances`
//!    (`SynthInstance.lean:201-211`) hands `getUnify` the CLASS
//!    APPLICATION itself, whose own arguments are the class's declared
//!    (non-instance) parameters — an instance's `[..]` HYPOTHESES never
//!    syntactically occur in that expression at all. So for this plan's
//!    own corpus, filtered and unfiltered query-path computation are
//!    trivially IDENTICAL, not just equivalent-under-`Star`.
//!
//! If a later plan's goal shape ever needs the ACTUAL oracle-unfiltered
//! `getUnifyKeyArgs` (e.g. indexing raw method-application terms like
//! `Add.add N inst x y` for simp/rw), that is a distinct, separately
//! named function to add alongside this one — not a reason to change
//! `mk_path` itself, which point 1 above already commits to being the
//! `pushArgs` transcription.
//!
//! # Reducible transparency
//!
//! `mkPath` runs its whole traversal under `withReducible`
//! (Main.lean:151-153); `mk_path` below saves/restores
//! `self.cfg.transparency` around the same span (Global Constraints:
//! restore any transparency override).
//!
//! # Named seams (documented, safe, never a wrong answer)
//!
//! - `hasNoindexAnnotation`/`mkNoindexAnnotation` (Main.lean:249-250,
//!   :290-291) — the user-facing `no_index` mdata marker. This crate has
//!   no such annotation-detection helper and no caller ever produces one
//!   (`noIndexAtArgs` is always `false` here, matching `mkPath`'s own
//!   default, Main.lean:152). Never checked; a `no_index`-annotated
//!   subterm is simply indexed structurally instead of being forced to
//!   `Star` — extra (not fewer) path positions, still individually
//!   correct, so this can only under-collapse, never mismatch.
//! - `isClass` (Main.lean:290) — gates whether a class projection's OWN
//!   structure argument is `no_index`-annotated. Always `false`: no
//!   class registry exists in this crate (same posture as
//!   `is_def_eq_singleton`'s own `isClass` elision, `lazy_delta.rs`).
//! - `isClass?` — SECOND, INDEPENDENT dependency (do not conflate with
//!   the `isClass` seam directly above, which is only the `.proj` arm's
//!   `no_index` gate): `ignoreArg`'s `Implicit`/`StrictImplicit` case
//!   (Main.lean:107-112) reads `ParamInfo.isInstance`, and
//!   `ParamInfo.isInstance` is NOT a `binderInfo == instImplicit` test —
//!   unlike `isImplicit`/`isStrictImplicit`/`isExplicit`, which really
//!   are (`Meta/Basic.lean:282-292`). `isInstance` is COMPUTED
//!   (`FunInfo.lean:111`): `className?.isSome && !decl.binderInfo.
//!   isExplicit`, i.e. "the parameter's TYPE is a registered class AND
//!   the binder is not `Default`" — deliberately not a pure binder-info
//!   test, per `FunInfo.lean:91-108`'s own worked examples: an implicit
//!   binder over a class type (`{_ : Hashable α}`) must still count as
//!   an instance, while `structure … extends`-generated constructors use
//!   EXPLICIT binders for their class-typed superclass fields, which
//!   must NOT count as instances.
//!
//!   `ignore_arg` below approximates `isInstance ≈ (binderInfo ==
//!   InstImplicit)` (its `Some(BinderInfo::InstImplicit) => Ok(true)`
//!   arm) because this crate has no class registry (`isClass?` needs
//!   one) to consult — same gap as the `isClass` seam above, just
//!   surfacing at a different call site. Four-case check of where this
//!   approximation lands relative to the oracle, `a` the argument value:
//!
//!   1. `[x : C]` (`InstImplicit`), `C` a class → oracle `true`
//!      (`isInstance`); code `true` (`InstImplicit` arm). Agree — the
//!      common case, and the only one this module's tests exercise.
//!   2. `{x : C}` (`Implicit`), `C` a class → oracle `true`
//!      (`isInstance`, per the `Hashable`/`OrdSet` example above); code
//!      falls to the `Implicit` arm, `!is_type(a)` — an instance VALUE's
//!      type is `C args`, not a `Sort`, so `is_type(a) == false` and the
//!      arm returns `true` too. Agree, but by ACCIDENT (via `is_type`,
//!      not via any class check) rather than by construction.
//!   3. `(x : C)` (`Default`, explicit), any `C` → oracle `false`
//!      (`!decl.binderInfo.isExplicit` is `false`), i.e. `isProof a`;
//!      code's `Default` arm is also `is_proof(a)`. Agree.
//!   4. `[x : T]` (`InstImplicit`), `T` NOT a class → oracle `false`
//!      (`className?` is `none`), i.e. `isProof a`; code's
//!      `InstImplicit` arm still returns `true` unconditionally.
//!      **DIVERGES**: the approximation stars a position the oracle
//!      would index structurally.
//!
//!   Case 4 is the only divergence, and it is QUERY-side superset-safe
//!   (point 2 below: a `Star` query key only ever visits a superset of
//!   what the real key would). **It would NOT be safe for insertion**:
//!   an insert-side `mk_path` call that hits case 4 would STORE `Star`
//!   at a position the oracle stores a real, structural key at — a
//!   wrong stored key, not merely a permissive query. `mk_path`
//!   is `pub(crate)` and currently query-side only (see "Insert-side vs.
//!   query-side" above), so this cannot bite today, but **any future
//!   insert-side use of `mk_path` (a future simp/rw indexer, per this
//!   module's own "reusable for other consumers" framing above) must
//!   first resolve `isClass?` properly** — i.e. own a real class
//!   registry — before reusing `ignore_arg` for insertion. No such
//!   registry exists anywhere in `leanr_meta` today; this is M4b/future
//!   work, not a task number this plan owns.
//! - `toNatLit?`/`isNumeral`/`shouldAddAsStar`/`isOffset`
//!   (Main.lean:126-198) — Nat-literal/offset recognition that collapses
//!   a numeral-shaped subterm to a single `Lit`/`Star` key. Always
//!   `None`/`false`: `to_nat_lit`/`should_add_as_star` below. A missed
//!   collapse only means MORE, still individually-correct path
//!   positions (the numeral recurses structurally as `Nat.succ (Nat.succ
//!   ..)`/`OfNat.ofNat ..` instead of one `Lit`), so this is strictly
//!   incompleteness (fewer trie matches for numeral-shaped queries),
//!   never a wrong key. Not exercised by `Instances.lean` (no numeral
//!   literals in the fixture).
//! - `etaExpandedStrict?` (Main.lean:196, :216-217) — `reduce`/
//!   `reduceUntilBadKey`'s retry-after-eta-reduction step. No
//!   eta-expansion-detection helper exists in this crate; `reduce`/
//!   `reduce_until_bad_key` below implement everything else in both
//!   functions (the `whnfCore`/`unfoldDefinition?` loop, and
//!   `reduceUntilBadKey`'s `isBadKey`-gated early stop) but never retry
//!   after an eta-strict collapse. Affects only terms that are exactly a
//!   strict eta-expansion of something with a better key — incompleteness
//!   only.
//! - `isAlwaysZero`'s general `max`/`imax`-recursive form and
//!   `instantiateLevelMVars` (InferType.lean:261-267, :326, inside
//!   `isProp`) — `is_proof` below delegates to the EXISTING
//!   `MetaCtx::is_prop` (`lazy_delta.rs`, already
//!   `isDefEqProofIrrel`'s own `isProp` transcription) rather than a
//!   second copy; that function's own doc comment already narrows
//!   `isAlwaysZero` to the literal `Level::Zero` case (never wrong, only
//!   incomplete for a non-normalized-but-provably-zero `max`/`imax`
//!   universe) and skips `instantiateLevelMVars`. Reusing it means
//!   `ignoreArg`'s `isProof` check inherits that same, already-reviewed
//!   narrowing rather than introducing an independent one.
//! - `getFunInfoNArgs`'s dependent-telescope substitution
//!   (`FunInfo.lean`): `param_binder_infos` below peels `Forall` binders
//!   to collect `BinderInfo` per position WITHOUT instantiating earlier
//!   binders into later ones (no fresh fvars minted, unlike the oracle's
//!   `forallBoundedTelescope`). This is safe because `ignoreArg` only
//!   ever reads a binder's OWN `BinderInfo` (an intrinsic property of
//!   the `Forall` node itself, never dependent on substitution) — never
//!   its (possibly bvar-mentioning) `binder_type`. The only way this
//!   under-counts binders is a function type whose later binders are
//!   hidden behind a `whnf` that itself depends on substituting an
//!   earlier binder — a shape no real Lean function TYPE (as opposed to
//!   its arguments) exhibits; every declaration's own Pi telescope is
//!   syntactically nested `Forall`s all the way down. Residual risk this
//!   substitution omission does NOT cover: when the peeled `body` is not
//!   syntactically a `Forall`, `param_binder_infos` calls `self.whnf` on
//!   it directly, and that `body` carries loose bvars from the binder(s)
//!   already peeled off — i.e. `whnf` runs on an open term there. For
//!   every real declaration type this branch is unreachable (nested
//!   `Forall`s all the way down, per the paragraph above), so the
//!   practical outcome is at worst the early-stop incompleteness already
//!   described; a `whnf` implementation that behaved badly on open terms
//!   could in principle surface a spurious `Forall` and thus a wrong
//!   `BinderInfo`, but no such behavior is known to exist here.
//!
//! # Landed ahead of its consumer
//!
//! `mk_path`/`discr_get_match` are `pub(crate)` per this task's own
//! interface spec (not part of `leanr_meta`'s external API), and PR-B's
//! instance table (task B3) — the real, non-test call site — has not
//! landed yet. Until it does, every item in this module is reachable
//! only from this module's own `#[cfg(test)]` tests, which the plain
//! `lib`/`lib test` clippy/rustc targets do not count as a "live root"
//! for the former. `#![allow(dead_code)]` below is scoped to this one
//! module (an inner attribute on the `discr_path` module, not the whole
//! crate) and should be removed once B3 wires this module in.
#![allow(dead_code)]

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::{BinderInfo, Literal};
use leanr_olean::DiscrKey;

use crate::discr_tree::DiscrTree;
use crate::{MVarId, MVarKind, MetaCtx, MetaError, TransparencyMode};

/// One pending flattened-path position: either a real subterm still to
/// be recursed into via [`MetaCtx::push_args`], or an already-decided
/// `Star` leaf. Stands in for the oracle's `todo : Array Expr` plus its
/// `tmpStar` marker-expression trick (Main.lean:70-71): rather than
/// minting a scratch metavariable expression just to route it back
/// through the same `.mvar tmpMVarId => .star` arm `pushArgs` itself
/// would take, `ignoreArg`'s verdict is recorded directly as this
/// variant — observably identical (a `Star` key, zero further
/// recursion) without the round-trip through the `Store`.
enum PathTodo {
    Expr(ExprId),
    Star,
}

impl<'e> MetaCtx<'e> {
    /// oracle: `mkPath` (Main.lean:151-153). Query-side path computation
    /// for a synthesis goal — see this module's doc comment for why this
    /// is the `pushArgs`/`ignoreArg` transcription, and how it relates to
    /// B1's `getUnify` transcription.
    pub(crate) fn mk_path(&mut self, e: ExprId) -> Result<Vec<DiscrKey>, MetaError> {
        let saved = self.cfg.transparency;
        self.cfg.transparency = TransparencyMode::Reducible;
        let r = self.mk_path_aux(e);
        self.cfg.transparency = saved;
        r
    }

    /// `discr_get_match` = `tree.get_match_keys(&mk_path(goal)?)` — the
    /// bridge the brief specifies between this module and B1's trie.
    pub(crate) fn discr_get_match<'a, V>(
        &mut self,
        tree: &'a DiscrTree<V>,
        goal: ExprId,
    ) -> Result<Vec<&'a V>, MetaError> {
        let path = self.mk_path(goal)?;
        Ok(tree.get_match_keys(&path))
    }

    /// oracle: `mkPathAux` (Main.lean:139-145), driven over an explicit
    /// `Vec` stack in place of the oracle's `Array` + recursion (same
    /// non-Rust-recursive shape as B1's own `process`/`getUnify` loop —
    /// no `guarded` needed here: this loop never grows the Rust call
    /// stack per iteration, only `self.step()`'s deterministic budget
    /// bounds it).
    fn mk_path_aux(&mut self, e: ExprId) -> Result<Vec<DiscrKey>, MetaError> {
        let mut todo = vec![PathTodo::Expr(e)];
        let mut keys = Vec::new();
        // oracle: `mkPathAux (root := true) (todo.push e) keys` for the
        // FIRST element only; every recursive call passes `root := false`
        // (Main.lean:145) — the initial element `e` is the only `root`
        // position.
        let mut root = true;
        while let Some(item) = todo.pop() {
            self.step()?;
            let key = match item {
                PathTodo::Star => DiscrKey::Star,
                PathTodo::Expr(cur) => self.push_args(root, cur, &mut todo)?,
            };
            keys.push(key);
            root = false;
        }
        Ok(keys)
    }

    /// oracle: `pushArgs` (Main.lean:267-311). `hasNoindexAnnotation`/
    /// `noIndexAtArgs` are named seams (module doc) — always "not
    /// annotated"/`false` here.
    fn push_args(
        &mut self,
        root: bool,
        e: ExprId,
        todo: &mut Vec<PathTodo>,
    ) -> Result<DiscrKey, MetaError> {
        let e = self.reduce_dt(root, e)?;
        let fn_ = self.get_app_fn(e);
        match self.node(fn_) {
            Node::LitNat { v } => {
                let n = self.scratch.nat_at(Some(self.view.store), v).clone();
                Ok(DiscrKey::Lit(Literal::NatVal(n)))
            }
            Node::LitStr { v } => {
                let s = self.scratch.str_at(Some(self.view.store), v).to_string();
                Ok(DiscrKey::Lit(Literal::StrVal(s)))
            }
            Node::Const { name: Some(c), .. } => {
                if !root {
                    if let Some(lit) = self.to_nat_lit(e)? {
                        return Ok(DiscrKey::Lit(lit));
                    }
                    if self.should_add_as_star(c, e)? {
                        return Ok(DiscrKey::Star);
                    }
                }
                let args = self.get_app_args(e);
                let nargs = args.len();
                self.push_args_aux(fn_, &args, todo)?;
                Ok(DiscrKey::Const {
                    name: c,
                    arity: nargs,
                })
            }
            Node::FVar { id: Some(_) } => {
                let args = self.get_app_args(e);
                let nargs = args.len();
                self.push_args_aux(fn_, &args, todo)?;
                Ok(DiscrKey::Fvar { arity: nargs })
            }
            // oracle: `.mvar mvarId => ..` (Main.lean:302-307). The
            // `mvarId == tmpMVarId` arm is unreachable here — this crate
            // never mints a `tmpStar`-style marker expr (see
            // `PathTodo`'s own doc comment).
            Node::MVar { id: Some(nid) } => {
                let synthetic_opaque = matches!(
                    self.mctx.decl(MVarId(nid)).map(|d| d.kind),
                    Some(MVarKind::SyntheticOpaque)
                );
                // oracle: `mvarId.isReadOnlyOrSyntheticOpaque` — `isReadOnly`
                // is the tier-1 seam this crate carries everywhere
                // (`level.rs`'s module doc, `assign.rs:140-148`'s own
                // "collapses to `kind == SyntheticOpaque`" precedent):
                // always `false` here, no depth-scoping concept exists.
                if synthetic_opaque {
                    Ok(DiscrKey::Other)
                } else {
                    Ok(DiscrKey::Star)
                }
            }
            Node::Forall { binder_type, .. } => {
                // oracle: `.forallE _n d _ _ => (.arrow, todo.push d)`
                // (Main.lean:308-309) — only the DOMAIN is pushed, never
                // the codomain (matches `discr_tree.rs::key_arity`'s own
                // `Arrow => 1` citation).
                todo.push(PathTodo::Expr(binder_type));
                Ok(DiscrKey::Arrow)
            }
            Node::Proj {
                type_name: Some(tn),
                idx,
                structure,
            } => self.push_proj(fn_, tn, idx as usize, structure, e, todo),
            Node::ProjBig {
                type_name: Some(tn),
                idx,
                structure,
            } => {
                // A `.proj` index that doesn't fit `usize` is malformed
                // decoded data (no real structure has that many fields);
                // erroring here (rather than substituting a bogus
                // `usize::MAX` sentinel and silently mis-keying the
                // path) matches this crate's never-silently-wrong
                // discipline for out-of-range decodes elsewhere.
                let idxv = self
                    .scratch
                    .nat_at(Some(self.view.store), idx)
                    .to_usize()
                    .ok_or_else(|| {
                        MetaError::Olean(format!(
                            "ProjBig index does not fit usize: {:?}",
                            self.scratch.nat_at(Some(self.view.store), idx)
                        ))
                    })?;
                self.push_proj(fn_, tn, idxv, structure, e, todo)
            }
            // oracle: `| _ => return (.other, todo)` (Main.lean:311) —
            // catches `.sort`/`.lam`/`.letE`/anonymous `.mvar`/anonymous
            // `.fvar`/malformed-`type_name` `.proj`/etc.
            _ => Ok(DiscrKey::Other),
        }
    }

    /// The `.proj` arm of `push_args` (Main.lean:290-296), factored out
    /// since `Proj`/`ProjBig` share everything but the index's own
    /// storage width. `isClass` is a named seam (module doc): always
    /// `false`, so `structure` is pushed as a real subterm, never
    /// `no_index`-annotated.
    fn push_proj(
        &mut self,
        fn_: ExprId,
        type_name: NameId,
        index: usize,
        structure: ExprId,
        e: ExprId,
        todo: &mut Vec<PathTodo>,
    ) -> Result<DiscrKey, MetaError> {
        // oracle: `push (.proj s i nargs) nargs (todo.push a)` — `a`
        // (the structure) is pushed FIRST, then `push`'s own `nargs`
        // further-applied args land on top of it, so `a` itself is the
        // LAST of this group to be popped (see `push_args_aux`'s own doc
        // comment on final pop order).
        todo.push(PathTodo::Expr(structure));
        let args = self.get_app_args(e);
        let nargs = args.len();
        self.push_args_aux(fn_, &args, todo)?;
        Ok(DiscrKey::Proj {
            structure: type_name,
            index,
            arity: nargs,
        })
    }

    /// oracle: `pushArgsAux` (Main.lean:114-119), fused with the
    /// `ignoreArg` substitution decision inline (see `PathTodo`'s doc
    /// comment for why no marker expression is minted).
    ///
    /// Pop-order note: the oracle recurses right-to-left over the
    /// application spine (`i = nargs-1` downTo `0`), pushing each
    /// decided value onto the SAME growing array the recursion is
    /// walking away from — so `args[nargs-1]`'s value is pushed FIRST
    /// (deepest) and `args[0]`'s value is pushed LAST (topmost). Since
    /// `mkPathAux`/`process` both pop from the BACK (LIFO), the actual
    /// PROCESSING order is `args[0]`, `args[1]`, ..., `args[nargs-1]` —
    /// left-to-right, declaration order (matches the module doc's own
    /// worked example: `⟨Add.add, 4⟩, α, *, x, y`). We reproduce this by
    /// pushing `args.iter().enumerate().rev()` onto our own LIFO `Vec`.
    fn push_args_aux(
        &mut self,
        head: ExprId,
        args: &[ExprId],
        todo: &mut Vec<PathTodo>,
    ) -> Result<(), MetaError> {
        if args.is_empty() {
            return Ok(());
        }
        let infos = self.param_binder_infos(head, args.len())?;
        for (i, &a) in args.iter().enumerate().rev() {
            if self.ignore_arg(a, i, &infos)? {
                todo.push(PathTodo::Star);
            } else {
                todo.push(PathTodo::Expr(a));
            }
        }
        Ok(())
    }

    /// oracle: `ignoreArg` (Main.lean:105-115). `infos.get(i)` standing
    /// in for the oracle's `if h : i < infos.size then infos[i] else ..`
    /// — both fall to the same "treat as a plain explicit argument, only
    /// check `isProof`" branch once `i` runs past the available
    /// `ParamInfo`s (an over-applied head).
    ///
    /// The `InstImplicit` arm below is an APPROXIMATION of the oracle's
    /// `ParamInfo.isInstance` (which is not a `BinderInfo` test at all —
    /// see the module doc's "Named seams" list, `isClass?` entry, for
    /// the full four-case divergence analysis and why it is query-side
    /// safe but not insert-side safe).
    fn ignore_arg(&mut self, a: ExprId, i: usize, infos: &[BinderInfo]) -> Result<bool, MetaError> {
        match infos.get(i) {
            Some(BinderInfo::InstImplicit) => Ok(true),
            Some(BinderInfo::Implicit) | Some(BinderInfo::StrictImplicit) => Ok(!self.is_type(a)?),
            Some(BinderInfo::Default) | None => self.is_proof(a),
        }
    }

    /// Stand-in for `getFunInfoNArgs`'s `ParamInfo.isImplicit`/
    /// `isStrictImplicit`/`isExplicit` fields (`Meta/Basic.lean:282-292`),
    /// which really are `binderInfo ==`-tests, reduced to exactly the raw
    /// `BinderInfo` of each of `head`'s first `nargs` `Forall` binders,
    /// peeled via `infer_type` and `whnf` together (the `infer_app_type`,
    /// `InferType.lean:106-116`, idiom: use the CURRENT type directly if
    /// it is already a `Forall`, else `whnf` once to try to expose one).
    /// NOTE: `ParamInfo.isInstance` (`FunInfo.lean:111`) is NOT one of
    /// these `binderInfo ==` fields — it is a computed
    /// `isClass?-and-non-explicit` predicate this crate cannot decide
    /// (no class registry); `ignore_arg`'s `InstImplicit` arm
    /// approximates it with a `BinderInfo` test anyway. See the module
    /// doc's "Named seams" `isClass?` entry for the resulting divergence.
    /// Stops early (returning fewer than `nargs` entries) if the type
    /// runs out of binders — `ignoreArg` treats a missing entry the same
    /// way (see its own doc comment). No telescope substitution is
    /// performed; see this module's doc comment (the `getFunInfoNArgs`
    /// seam entry, which also covers the residual `whnf`-on-an-open-term
    /// risk below) for why that's sound here.
    fn param_binder_infos(
        &mut self,
        head: ExprId,
        nargs: usize,
    ) -> Result<Vec<BinderInfo>, MetaError> {
        let mut infos = Vec::with_capacity(nargs);
        let mut ty = self.infer_type(head)?;
        for _ in 0..nargs {
            let ty_forall = if matches!(self.node(ty), Node::Forall { .. }) {
                ty
            } else {
                self.whnf(ty)?
            };
            match self.node(ty_forall) {
                Node::Forall {
                    binder_info, body, ..
                } => {
                    infos.push(binder_info);
                    ty = body;
                }
                _ => break,
            }
        }
        Ok(infos)
    }

    /// oracle: `isType` (InferType.lean:502-511), skipping the `isTypeQuick`
    /// fast path (a pure optimization over the same final answer — see
    /// this module's doc comment on why every seam here is safety-neutral).
    /// `whnf_default` (`pub(crate)`, `whnf.rs:1548`, oracle `whnfD`) forces
    /// `.default` transparency for the TYPE's own whnf regardless of
    /// `mk_path`'s ambient `.reducible` setting, saving/restoring around
    /// just that one nested call — the same primitive `is_proof`/`is_prop`
    /// below reuse (via the existing `MetaCtx::is_prop`) rather than a
    /// second hand-rolled save/restore.
    fn is_type(&mut self, e: ExprId) -> Result<bool, MetaError> {
        let ty = self.infer_type(e)?;
        let w = self.whnf_default(ty)?;
        Ok(matches!(self.node(w), Node::Sort { .. }))
    }

    /// oracle: `isProof` (InferType.lean:448-451), skipping `isProofQuick`
    /// (same "optimization only" posture as `is_type` above): `isProof e
    /// = isProp (inferType e)`. `MetaCtx::is_prop` (`lazy_delta.rs`,
    /// already `isDefEqProofIrrel`'s own transcription of `isProp`,
    /// InferType.lean:323-330) is reused directly rather than duplicated —
    /// same narrowing it already documents (`isAlwaysZero` narrowed to
    /// literal `Level::Zero`, not the general `max`/`imax`-recursive
    /// predicate): incompleteness-only, and this task's own fixture never
    /// needs the general case either.
    fn is_proof(&mut self, e: ExprId) -> Result<bool, MetaError> {
        let ty = self.infer_type(e)?;
        self.is_prop(ty)
    }

    /// oracle: `reduceDT` (Main.lean:213-214).
    fn reduce_dt(&mut self, root: bool, e: ExprId) -> Result<ExprId, MetaError> {
        if root {
            self.reduce_until_bad_key(e)
        } else {
            self.reduce(e)
        }
    }

    /// oracle: `reduce` (Main.lean:196-203), minus `etaExpandedStrict?`
    /// (named seam, module doc). `whnfCore`/`unfoldDefinition?` are
    /// EXPLICITLY reused rather than the public `MetaCtx::whnf`: `whnf`
    /// (`whnfImp`) ALSO calls `reduce_nat?` between them (`whnf.rs`'s own
    /// `whnf_imp`), a step the oracle's `DiscrTree.reduce` never takes —
    /// reusing `whnf` here would silently fold `Nat.add`/`Nat.succ`
    /// literal arithmetic that the real `DiscrTree.reduce` does not.
    fn reduce(&mut self, mut e: ExprId) -> Result<ExprId, MetaError> {
        loop {
            self.step()?;
            let w = self.whnf_core(e)?;
            match self.unfold_definition(w)? {
                Some(e2) => e = e2,
                None => return Ok(w),
            }
        }
    }

    /// oracle: `reduceUntilBadKey`/`step` (Main.lean:216-226), minus
    /// `etaExpandedStrict?` (same seam as [`Self::reduce`]).
    fn reduce_until_bad_key(&mut self, mut e: ExprId) -> Result<ExprId, MetaError> {
        loop {
            self.step()?;
            let w = self.whnf_core(e)?;
            match self.unfold_definition(w)? {
                Some(e2) => {
                    let head2 = self.get_app_fn(e2);
                    // oracle: `if isBadKey e'.getAppFn then return e else
                    // step e'` — `e` here is `step`'s OWN local, i.e. the
                    // whnf_core'd term `w`, not the original input.
                    if self.is_bad_key(head2) {
                        return Ok(w);
                    }
                    e = e2;
                }
                None => return Ok(w),
            }
        }
    }

    /// oracle: `isBadKey` (Main.lean:206-212).
    fn is_bad_key(&self, fn_: ExprId) -> bool {
        !matches!(
            self.node(fn_),
            Node::LitNat { .. }
                | Node::LitStr { .. }
                | Node::Const { .. }
                | Node::FVar { .. }
                | Node::Proj { .. }
                | Node::ProjBig { .. }
                | Node::Forall { .. }
        )
    }

    /// SEAM: oracle `toNatLit?` (Main.lean:141-148, via `isNumeral`,
    /// Main.lean:126-140) — see module doc's "Named seams" list. Always
    /// `None`. `&self` (not `&mut self`): the oracle's own `toNatLit?`/
    /// `isNumeral` are PURE `Expr -> Option Literal`/`Expr -> Bool`
    /// functions, not `MetaM` — no monadic effect (whnf, etc.) is ever
    /// needed to decide "is this syntactically a numeral", so this stub's
    /// signature already matches what a full transcription would need.
    fn to_nat_lit(&self, _e: ExprId) -> Result<Option<Literal>, MetaError> {
        Ok(None)
    }

    /// SEAM: oracle `shouldAddAsStar`/`isOffset` (Main.lean:189-198) —
    /// see module doc's "Named seams" list. Always `false`.
    fn should_add_as_star(&mut self, _c: NameId, _e: ExprId) -> Result<bool, MetaError> {
        Ok(false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::{const_dotted, const_named, with_instances_ctx};

    /// Step-1 test from the task brief: the goal `Add N`'s path must
    /// head with `Const Add 1` (`Add` takes exactly one explicit
    /// argument — `class Add (a : Type u) where ..` — confirmed against
    /// the fixture's own decoded type, NOT two as the brief's own
    /// illustrative sketch guessed; the brief itself flags its helper
    /// names/shapes as suggestions, not requirements).
    #[test]
    fn mk_path_heads_on_the_class() {
        with_instances_ctx(|ctx| {
            let add = const_named(ctx, "Add");
            let n = const_named(ctx, "N");
            let goal = ctx.mk_app_spine(add, &[n]).expect("Add N");
            let path = ctx.mk_path(goal).expect("mk_path");
            assert!(
                matches!(path.first(), Some(DiscrKey::Const { name, arity: 1 })
                    if crate::test_support::render_name(ctx, *name) == "Add"),
                "path: {path:?}"
            );
        });
    }

    /// Risk-6 pin: `instAddProd {a b : Type u} [Add a] [Add b] : Add
    /// (Prod a b)`'s own two `[Add a] [Add b]` instance-implicit
    /// arguments (confirmed `InstImplicit` against the fixture's decoded
    /// type) must become bare `Star` keys — not recurse into `instAddN`'s
    /// own structure — while the two preceding `Type u`-valued implicit
    /// arguments (`a`, `b`) ARE indexed structurally (`ignoreArg`'s
    /// implicit-but-a-type carve-out, Main.lean:107-112's own worked
    /// `Decidable (@Eq Nat x y)` example). Applying `instAddProd` itself
    /// (rather than its RESULT type `Add (Prod a b)`) puts all four of
    /// its own binders one level away from the head, in the exact shape
    /// `ignoreArg` inspects.
    #[test]
    fn ignore_arg_stars_the_instance_implicit_positions() {
        with_instances_ctx(|ctx| {
            let inst_add_prod = const_named(ctx, "instAddProd");
            let n = const_named(ctx, "N");
            let inst_add_n = const_named(ctx, "instAddN");
            let goal = ctx
                .mk_app_spine(inst_add_prod, &[n, n, inst_add_n, inst_add_n])
                .expect("instAddProd N N instAddN instAddN");

            let path = ctx.mk_path(goal).expect("mk_path");

            let n_name = if let Node::Const { name: Some(nm), .. } = ctx.node(n) {
                nm
            } else {
                panic!("N is not a bare const")
            };
            assert_eq!(
                path,
                vec![
                    DiscrKey::Const {
                        name: {
                            if let Node::Const { name: Some(nm), .. } = ctx.node(inst_add_prod) {
                                nm
                            } else {
                                panic!("instAddProd is not a bare const")
                            }
                        },
                        arity: 4,
                    },
                    DiscrKey::Const {
                        name: n_name,
                        arity: 0,
                    },
                    DiscrKey::Const {
                        name: n_name,
                        arity: 0,
                    },
                    DiscrKey::Star,
                    DiscrKey::Star,
                ],
                "path: {path:?}"
            );
        });
    }

    /// `mk_path` must restore `self.cfg.transparency` exactly (Global
    /// Constraints: never leak a transparency override).
    #[test]
    fn mk_path_restores_transparency() {
        with_instances_ctx(|ctx| {
            let saved = ctx.cfg().transparency;
            let add = const_named(ctx, "Add");
            let n = const_named(ctx, "N");
            let goal = ctx.mk_app_spine(add, &[n]).expect("Add N");
            ctx.mk_path(goal).expect("mk_path");
            assert_eq!(ctx.cfg().transparency, saved);
        });
    }

    /// Pins the OTHER half of risk 6 (`mk_path_restores_transparency`
    /// above only pins save/restore, which passes even if `mk_path`
    /// never overrode transparency at all): the traversal must actually
    /// RUN at reducible-tier transparency, not the ambient
    /// `Config::default()` (`TransparencyMode::Default`). `id {α : Sort
    /// u} (a : α) : α := a` is a plain `def` with no reducibility
    /// attribute — `Semireducible` status — so it is NOT unfoldable at
    /// `.reducible`/`.instances`/`.implicit` (`can_unfold`,
    /// `transparency.rs`) but IS unfoldable at the ambient `.default`.
    /// If `mk_path` ran at `.default` (e.g. the override were dropped or
    /// a no-op), `reduce_until_bad_key` would delta-unfold `id N N.zero`
    /// all the way to `N.zero`, and this test would see `Const N 0` as
    /// the head instead of `Const id 2` — the assertion below is a real,
    /// falsifiable probe of the transparency actually in effect, not a
    /// vacuous one.
    #[test]
    fn mk_path_does_not_unfold_a_semireducible_def_at_reducible_transparency() {
        with_instances_ctx(|ctx| {
            let id = const_named(ctx, "id");
            let n = const_named(ctx, "N");
            let n_zero = const_dotted(ctx, "N", "zero");
            let goal = ctx.mk_app_spine(id, &[n, n_zero]).expect("id N N.zero");

            let path = ctx.mk_path(goal).expect("mk_path");

            let id_name = if let Node::Const { name: Some(nm), .. } = ctx.node(id) {
                nm
            } else {
                panic!("id is not a bare const")
            };
            let n_name = if let Node::Const { name: Some(nm), .. } = ctx.node(n) {
                nm
            } else {
                panic!("N is not a bare const")
            };
            let n_zero_name = if let Node::Const { name: Some(nm), .. } = ctx.node(n_zero) {
                nm
            } else {
                panic!("N.zero is not a bare const")
            };
            assert_eq!(
                path,
                vec![
                    DiscrKey::Const {
                        name: id_name,
                        arity: 2,
                    },
                    DiscrKey::Const {
                        name: n_name,
                        arity: 0,
                    },
                    DiscrKey::Const {
                        name: n_zero_name,
                        arity: 0,
                    },
                ],
                "path: {path:?} — if this shows a Const N/N.zero head instead \
                 of Const id, mk_path is running at .default (or another \
                 non-reducible-tier mode), not .reducible"
            );
        });
    }

    /// Companion to the test above, ruling out the OTHER failure
    /// direction (`.none`, which would also leave a `Semireducible` `id`
    /// unreduced, so the test above alone can't distinguish `.none` from
    /// `.reducible`): `abbrev Unit : Type := PUnit` desugars to a
    /// `@[reducible] def`, so it IS unfoldable at `.reducible` (and every
    /// coarser mode) but NOT at `.none`. Together, the two tests pin the
    /// traversal to the reducible tier (`.reducible`/`.instances`/
    /// `.implicit` — the three are not distinguishable by any probe
    /// available in this fixture, but `mk_path`'s own source sets
    /// exactly `TransparencyMode::Reducible`, matching `mkPath`'s
    /// `withReducible`).
    #[test]
    fn mk_path_unfolds_a_reducible_abbrev_at_reducible_transparency() {
        with_instances_ctx(|ctx| {
            let unit = const_named(ctx, "Unit");
            let path = ctx.mk_path(unit).expect("mk_path");

            match path.first() {
                Some(DiscrKey::Const { name, arity: 0 }) => {
                    assert_eq!(
                        crate::test_support::render_name(ctx, *name),
                        "PUnit",
                        "path: {path:?}"
                    );
                }
                _ => panic!(
                    "expected Unit to unfold to PUnit under reducible transparency, path: {path:?}"
                ),
            }
        });
    }

    /// `Add.add`'s own auto-generated-projection shape (`{a : Type u} ->
    /// [self : Add a] -> a -> a -> a`) is the module doc's own worked
    /// example (`⟨Add.add, 4⟩, α, *, x, y`) — a second, independent
    /// pin of both left-to-right declaration order AND the
    /// instance-implicit skip, over a DIFFERENT head shape than
    /// `instAddProd` (a method projection, not an instance value).
    #[test]
    fn add_add_application_matches_the_module_docs_worked_example() {
        with_instances_ctx(|ctx| {
            let add_add = const_dotted(ctx, "Add", "add");
            let n = const_named(ctx, "N");
            let inst_add_n = const_named(ctx, "instAddN");
            let n_zero = const_dotted(ctx, "N", "zero");
            let goal = ctx
                .mk_app_spine(add_add, &[n, inst_add_n, n_zero, n_zero])
                .expect("Add.add N instAddN N.zero N.zero");

            let path = ctx.mk_path(goal).expect("mk_path");

            let n_name = if let Node::Const { name: Some(nm), .. } = ctx.node(n) {
                nm
            } else {
                panic!("N is not a bare const")
            };
            let n_zero_name = if let Node::Const { name: Some(nm), .. } = ctx.node(n_zero) {
                nm
            } else {
                panic!("N.zero is not a bare const")
            };
            assert_eq!(
                path,
                vec![
                    DiscrKey::Const {
                        name: {
                            if let Node::Const { name: Some(nm), .. } = ctx.node(add_add) {
                                nm
                            } else {
                                panic!("Add.add is not a bare const")
                            }
                        },
                        arity: 4,
                    },
                    DiscrKey::Const {
                        name: n_name,
                        arity: 0,
                    },
                    DiscrKey::Star,
                    DiscrKey::Const {
                        name: n_zero_name,
                        arity: 0,
                    },
                    DiscrKey::Const {
                        name: n_zero_name,
                        arity: 0,
                    },
                ],
                "path: {path:?}"
            );
        });
    }

    /// `discr_get_match` = `tree.get_match_keys(&mk_path(goal)?)`,
    /// exercised end-to-end against B1's own `DiscrTree`: an instance
    /// keyed under `[Const Add 1, Const N 0]` (mirroring what a decoded
    /// `InstanceEntry.keys` for `instAddN : Add N` would look like) is
    /// found by querying the goal `Add N`.
    #[test]
    fn discr_get_match_finds_an_instance_keyed_by_its_type() {
        with_instances_ctx(|ctx| {
            let add = const_named(ctx, "Add");
            let n = const_named(ctx, "N");
            let n_name = if let Node::Const { name: Some(nm), .. } = ctx.node(n) {
                nm
            } else {
                panic!("N is not a bare const")
            };
            let add_name = if let Node::Const { name: Some(nm), .. } = ctx.node(add) {
                nm
            } else {
                panic!("Add is not a bare const")
            };

            let mut tree: DiscrTree<&'static str> = DiscrTree::default();
            tree.insert(
                &[
                    DiscrKey::Const {
                        name: add_name,
                        arity: 1,
                    },
                    DiscrKey::Const {
                        name: n_name,
                        arity: 0,
                    },
                ],
                "instAddN",
            );

            let goal = ctx.mk_app_spine(add, &[n]).expect("Add N");
            let got = ctx.discr_get_match(&tree, goal).expect("discr_get_match");
            assert_eq!(got, vec![&"instAddN"]);
        });
    }
}
