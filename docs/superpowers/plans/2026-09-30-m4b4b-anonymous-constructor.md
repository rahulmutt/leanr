# M4b-4b Anonymous Constructor Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Elaborate the term-position anonymous constructor `⟨…⟩` so that it produces oracle-identical terms, including the nested flattening of extra arguments and postponement.

**Architecture:** A new elaborator, `builtin/anon_ctor.rs`, ports `elabAnonymousCtor`. It calls the constructor head directly (`mk_const` plus `app::elab_app_args`) and does not synthesize syntax. The oracle's synthesized nested `⟨extra,*⟩` is represented as "the outer node plus a start index". That index is carried by a crate-private `TermTarget` inside `elab.rs`, one new `Arg` variant, and one new field on `SyntheticMVarKind::Postponed`.

**Tech Stack:** Rust (`leanr_elab`), rowan syntax trees (`leanr_syntax`), and the pinned Lean oracle `leanprover/lean4:v4.33.0-rc1`, which is used to regenerate the fixtures.

**Spec:** `docs/superpowers/specs/2026-09-30-m4b4b-anonymous-constructor-design.md`. Read it first. § Evidence holds the measured oracle result for every term used below.

## Global Constraints

- Oracle pin: `leanprover/lean4:v4.33.0-rc1`. Never bump it. The oracle source is at `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/`, and the elaborator is `Lean/Elab/BuiltinNotation.lean:43-102`.
- Only `leanr_elab` and `tests/fixtures/elab/` change. `leanr_meta`, `leanr_syntax`, `leanr_olean` and `leanr_kernel` stay untouched.
- **Every oracle `file:line` you write in a comment must be opened and checked.** Citations in this repo have repeatedly been off by 1–2 lines, and the error spreads from plan to brief to comment.
- Before every commit, run `cargo fmt --all`. CI (`mise run ci`) gates on `cargo fmt --check` and `cargo clippy -D warnings`, and the test commands below do not cover either.
- Run `mise run ci` in the **foreground**, blocking until it exits. Never background it and end your turn: that loses the job.
- Build only under `/workspace`, never under `/tmp`. `/tmp` is a 20Gi EmptyDir, and a cargo target there has evicted the pod before.
- Named-seam discipline: an unported path returns `ElabError::UnsupportedSyntax` naming its owning slice. It never panics and never returns a guessed `ExprId`.
- Oracle prose is not ported. Errors are typed variants.
- Test commands run from `/workspace`.

## Review Focus

1. **Tail postponed under a binder:** `fun (n : Nat) => sameAs (⟨n, n, n⟩ : Prod Nat _) (Prod.mk n (Prod.mk n n))`. The resumed tail must see `n` through the saved context, and the result must not leak an fvar. The oracle accepts it (Task 2 corpus: `anon/tailUnderBinder`).
2. **An error raised inside a resumed tail must be reported, not swallowed:** `sameAs (⟨z, z, z⟩ : Prod Nat _) (Prod.mk z (fun x : Nat => x))`. The oracle reports "expected type `(x : Nat) → Nat` is not an inductive type" (Task 2 smoke).
3. **Implicit lambda around `⟨⟩`:** `(⟨z, z⟩ : {α : Type} → Prod Nat Nat)`. The oracle gives `fun {α} => @Prod.mk … z z` (Task 1 corpus: `anon/implicitLambda`).
4. **An explicit nested `⟨⟩` in a postponed argument:** `sameAs ⟨z, ⟨z, z⟩⟩ (Prod.mk z (Prod.mk z z))`. The oracle accepts it (Task 1 corpus: `anon/nestedPostponed`).
5. **Trivia inside the brackets:** `(⟨Nat.zero /- c -/ ,   Nat.zero⟩ : Prod Nat Nat)`. Separator filtering must ignore the comment and whitespace. The oracle gives `@Prod.mk … z z` (Task 1 corpus: `anon/trivia`).

Throughout the plan, `z` abbreviates `Nat.zero`. Every source string written into a file must spell out `Nat.zero`.

---

## File Structure

| File | Responsibility |
|---|---|
| `crates/leanr_elab/src/builtin/anon_ctor.rs` (new) | `elab_anon_ctor`, `anon_ctor_args`, `num_explicit_fields`: the port of `elabAnonymousCtor` |
| `crates/leanr_elab/src/builtin/mod.rs` | `pub mod anon_ctor;` |
| `crates/leanr_elab/src/dispatch.rs` | register and route `Lean.Parser.Term.anonymousCtor`; update the deferred-list doc |
| `crates/leanr_elab/src/error.rs` | `ElabError::InvalidAnonymousCtor(AnonCtorError)` and `enum AnonCtorError` |
| `crates/leanr_elab/src/lib.rs` | re-export `AnonCtorError`; update the deferred-list doc (`:139`) |
| `crates/leanr_elab/src/app/lval.rs` | widen `node`, `app_fn`, `render` from `pub(super)` to `pub(crate)` |
| `crates/leanr_elab/src/elab.rs` (Task 2) | `TermTarget`; thread it through `elab_term_core` / `elab_using_elab_fns` / `elab_implicit_lambda` |
| `crates/leanr_elab/src/postpone.rs` (Task 2) | `postpone_elab_term` takes a `TermTarget` and records `tail_from` |
| `crates/leanr_elab/src/synthetic/state.rs` (Task 2) | `Postponed { ctx, tail_from: Option<usize> }` |
| `crates/leanr_elab/src/synthetic/ladder.rs` (Task 2) | `resume_postponed` rebuilds the target from `(stx, tail_from)` |
| `crates/leanr_elab/src/app/expand.rs` (Task 2) | `Arg::AnonCtorTail { node, from }` |
| `crates/leanr_elab/src/app/propagate.rs`, `app/args.rs` (Task 2) | the new `Arg` arm at each match site |
| `tests/fixtures/elab/Elab0.lean` | new fixture declarations |
| `tests/fixtures/elab/dump_elab.lean` | `anonQueries` / `anonTailQueries` lists |
| `tests/fixtures/elab/elab-queries.jsonl`, `structures.jsonl`, `Elab0.olean` | regenerated |
| `crates/leanr_elab/tests/anon_ctor_smoke.rs` (new) | error variants, seams, the argument-shape probe |
| `crates/leanr_elab/tests/seam_audit.rs` (Task 3) | registered-kind flip, pattern seam, `M4b-4b` needle |
| `docs/superpowers/specs/2026-09-30-m4b4b-anonymous-constructor-design.md` (Task 3) | `## Landed` section |

---

### Task 1: Fixture, errors, and the exact-arity elaborator

This task ships everything except flattening. When the argument count exceeds the explicit-field count (with k > 0), the elaborator raises a temporary seam that Task 2 removes.

**Files:**
- Modify: `tests/fixtures/elab/Elab0.lean` (append at end of file)
- Modify: `tests/fixtures/elab/dump_elab.lean` (new list before `def emit`; add it to `main`'s query concatenation)
- Regenerate: `tests/fixtures/elab/Elab0.olean`, `elab-queries.jsonl`, `structures.jsonl`
- Create: `crates/leanr_elab/src/builtin/anon_ctor.rs`
- Modify: `crates/leanr_elab/src/builtin/mod.rs`, `src/dispatch.rs`, `src/error.rs`, `src/lib.rs`, `src/app/lval.rs:74,79,97`
- Create: `crates/leanr_elab/tests/anon_ctor_smoke.rs`

**Interfaces:**
- Produces (used by Task 2):
  - `pub(crate) fn elab_anon_ctor(elab: &mut TermElabM, node: &SyntaxNode, from: usize, kinds: &KindInterner, expected: Option<ExprId>) -> Result<ExprId, ElabError>` in `crate::builtin::anon_ctor`
  - `pub(crate) fn anon_ctor_args(node: &SyntaxNode, kinds: &KindInterner) -> Result<Vec<SynElem>, ElabError>`
  - `pub use error::AnonCtorError` from `leanr_elab`
  - the fixture names `And`, `Exists`, `True`, `Empty`, `ImpI`, `T3`, `PrivMk`, `sameAs`

- [ ] **Step 1: Add the fixture declarations.** Append to `tests/fixtures/elab/Elab0.lean`. First check with `grep -nE '^(structure|inductive|def|abbrev) (And|Exists|True|Empty|ImpI|T3|PrivMk|sameAs)\b' tests/fixtures/elab/Elab0.lean` that none of these names exist yet. It should print nothing.

```lean
-- M4b-4b: the anonymous constructor `⟨…⟩` (design spec
-- 2026-09-30-m4b4b-anonymous-constructor-design.md § Fixture).
-- `And`/`Exists`/`True` are Prop-valued single-constructor types
-- (`Exists` is not a structure); `Empty` has no constructors; `ImpI`'s
-- implicit field is not counted by `⟨⟩`; `T3` has three explicit fields
-- (nested InsufficientFields); `PrivMk`'s constructor is private;
-- `sameAs` forces its first argument to postpone.
structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b

inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p

inductive True : Prop where
  | intro : True

inductive Empty : Type

inductive ImpI : Type where
  | mk {n : Nat} (x : Nat) : ImpI

structure T3 where
  a : Nat
  b : Nat
  c : Nat

structure PrivMk where
  private mk ::
  x : Nat

def sameAs {α : Type} (a b : α) : α := b
```

- [ ] **Step 2: Add the Task 1 corpus queries.** In `tests/fixtures/elab/dump_elab.lean`, insert immediately before `def emit`:

```lean
-- M4b-4b task 1: the anonymous constructor, exact arity (no flattening).
-- `elabAnonymousCtor`, BuiltinNotation.lean:43-102. Every source was run
-- through the pinned oracle while writing the design spec (§ Evidence).
def anonQueries : List (String × String) :=
  [ ("anon/prod",            "(⟨Nat.zero, Nat.zero⟩ : Prod Nat Nat)")
  , ("anon/nestedExplicit",  "(⟨Nat.zero, ⟨Nat.zero, Nat.zero⟩⟩ : Prod Nat (Prod Nat Nat))")
  , ("anon/implicitField",   "(⟨Nat.zero⟩ : ImpI)")
  , ("anon/exists",          "(⟨Nat.zero, Eq.refl Nat.zero⟩ : Exists (fun n : Nat => Eq n Nat.zero))")
  , ("anon/and",             "(⟨True.intro, True.intro⟩ : And True True)")
  , ("anon/punit",           "(⟨⟩ : PUnit)")
  , ("anon/unitAlias",       "(⟨⟩ : Unit)")
  , ("anon/postponed",       "sameAs ⟨Nat.zero, Nat.zero⟩ (Prod.mk Nat.zero Nat.zero)")
  , ("anon/nestedPostponed", "sameAs ⟨Nat.zero, ⟨Nat.zero, Nat.zero⟩⟩ (Prod.mk Nat.zero (Prod.mk Nat.zero Nat.zero))")
  , ("anon/arg",             "Prod.fst ⟨Nat.zero, Nat.zero⟩")
  , ("anon/implicitLambda",  "(⟨Nat.zero, Nat.zero⟩ : {α : Type} -> Prod Nat Nat)")
  , ("anon/trivia",          "(⟨Nat.zero /- c -/ ,   Nat.zero⟩ : Prod Nat Nat)")
  ]
```

Then append `++ anonQueries` to the end of the `for (id, src) in … ++ p4Queries do` line in `main`.

- [ ] **Step 3: Regenerate the fixtures and check that every query produced a record.**

Run:
```bash
cd /workspace/tests/fixtures/elab && lean Elab0.lean -o Elab0.olean && cd /workspace && mise run fixtures:regen-elab 2>&1 | tail -5
grep -c '"id":"anon/' tests/fixtures/elab/elab-queries.jsonl
git diff --stat tests/fixtures/elab/
```
Expected:
- the grep prints `12`
- `regen-elab`'s stderr has no `dump_elab: … failed for anon/` line
- the diff touches only `Elab0.lean`, `Elab0.olean`, `dump_elab.lean`, `elab-queries.jsonl` (12 added lines, no other changes) and `structures.jsonl` (rows added for `And`, `T3`, `PrivMk`, with no existing row changed)

If any other record changed, stop and investigate: a new fixture name has collided with something.

- [ ] **Step 4: Run the corpus test to verify it fails.**

Run: `cargo test -p leanr_elab --test oracle_elab 2>&1 | tail -20`
Expected: FAIL. The 12 `anon/*` records report `UnsupportedSyntax("Lean.Parser.Term.anonymousCtor")`. Every other record passes. If a non-`anon` record fails, the fixture additions broke something, and that has to be fixed first.

- [ ] **Step 5: Write the failing smoke tests.** Create `crates/leanr_elab/tests/anon_ctor_smoke.rs`:

```rust
//! M4b-4b: anonymous-constructor rejections and seams. The corpus
//! (`oracle_elab.rs`) is success-only, so every oracle ERROR this slice
//! ports is pinned here by variant. Each case was run on the pinned
//! oracle (`lean` on a prelude-mode scratch file importing `Elab0`,
//! `LEAN_PATH=tests/fixtures/elab`, one `#check` per case) before it was
//! written; the oracle's message is quoted beside it. Design spec
//! § Evidence.

mod support;

use leanr_elab::{AnonCtorError, ElabError};

fn anon_err(src: &str) -> AnonCtorError {
    match support::elab_and_synthesize(src) {
        Err(ElabError::InvalidAnonymousCtor(e)) => e,
        other => panic!("{src}: expected InvalidAnonymousCtor, got {other:?}"),
    }
}

#[test]
fn expected_type_unknown() {
    // "Invalid `⟨...⟩` notation: The expected type of this term could not
    // be determined"
    assert_eq!(anon_err("⟨Nat.zero, Nat.zero⟩"), AnonCtorError::ExpectedTypeUnknown);
}

#[test]
fn not_inductive() {
    // "Invalid `⟨...⟩` notation: The expected type `Nat → Nat` is not an
    // inductive type"
    assert!(matches!(
        anon_err("(⟨Nat.zero⟩ : Nat -> Nat)"),
        AnonCtorError::NotInductive { .. }
    ));
}

#[test]
fn no_ctors_and_multiple_ctors() {
    // "… The expected type `Empty` has no constructors"
    assert!(matches!(anon_err("(⟨⟩ : Empty)"), AnonCtorError::NoCtors { .. }));
    // "… The expected type `Bool` has more than one constructor"
    assert!(matches!(anon_err("(⟨⟩ : Bool)"), AnonCtorError::MultipleCtors { .. }));
}

#[test]
fn insufficient_fields_top_level() {
    // "Insufficient number of fields for `⟨...⟩` constructor: Constructor
    // `Prod.mk` has 2 explicit field, but only 1 was provided". The
    // oracle logs this under `errToSorry` and pads with `sorry`; leanr
    // throws (spec § Architecture, step 7).
    assert_eq!(
        anon_err("(⟨Nat.zero⟩ : Prod Nat Nat)"),
        AnonCtorError::InsufficientFields {
            ctor: "Prod.mk".to_string(),
            explicit: 2,
            provided: 1
        }
    );
}

#[test]
fn no_explicit_fields() {
    // "Insufficient number of fields for `⟨...⟩` constructor: Constructor
    // `True.intro` does not have explicit fields, but 1 was provided"
    assert_eq!(
        anon_err("(⟨Nat.zero⟩ : True)"),
        AnonCtorError::NoExplicitFields {
            ctor: "True.intro".to_string(),
            provided: 1
        }
    );
}

/// `Eq`'s index is promoted to a parameter (`numParams = 2`), so `k = 0`
/// and `⟨⟩` becomes a bare `Eq.refl` whose explicit `a` stays unapplied:
/// the app elaborator's type mismatch, NOT `InsufficientFields`. This
/// is the test that catches "count from 0 instead of numParams".
/// Oracle: "Type mismatch\n  @Eq.refl ?m.2\nhas type\n  ∀ (a : ?m.2), …".
#[test]
fn eq_counts_fields_after_its_promoted_parameters() {
    match support::elab_and_synthesize("(⟨⟩ : Eq Nat.zero Nat.zero)") {
        Err(ElabError::TypeMismatch { .. }) => {}
        other => panic!("expected TypeMismatch, got {other:?}"),
    }
}

/// The oracle accepts a private constructor from its own module
/// (`_private.Anon.0.PrivMk.mk`); leanr models no private names, so any
/// `_private.` constructor is the crate-wide seam (spec § Architecture,
/// step 5).
#[test]
fn private_constructor_is_the_private_names_seam() {
    match support::elab_and_synthesize("(⟨Nat.zero⟩ : PrivMk)") {
        Err(ElabError::UnsupportedSyntax(m)) => {
            assert!(m.contains("private names"), "{m}")
        }
        other => panic!("expected the private-names seam, got {other:?}"),
    }
}
```

- [ ] **Step 6: Run the smoke tests to verify they fail.**

Run: `cargo test -p leanr_elab --test anon_ctor_smoke 2>&1 | tail -5`
Expected: compile error, because `AnonCtorError` and `ElabError::InvalidAnonymousCtor` don't exist yet.

- [ ] **Step 7: Add the error type.** In `crates/leanr_elab/src/error.rs`, add this variant to `enum ElabError`, directly after `InvalidDottedIdent { … },`:

```rust
    /// oracle: `elabAnonymousCtor`'s throws
    /// (`Lean/Elab/BuiltinNotation.lean:43-102`). Prose deferred (design
    /// spec 2026-09-30-m4b4b § Errors).
    InvalidAnonymousCtor(AnonCtorError),
```

Then add this after `enum InvalidDottedIdentReason`'s closing brace:

```rust
/// Which `elabAnonymousCtor` throw an `ElabError::InvalidAnonymousCtor`
/// stands for. `ctor` is the constructor's rendered name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AnonCtorError {
    /// `BuiltinNotation.lean:47-48`, thrown at `:54` (an mvar head after
    /// `whnf`) and `:101` (no expected type).
    ExpectedTypeUnknown,
    /// `:56-57` — `matchConstInduct`'s failure continuation.
    NotInductive { ty: ExprId },
    /// `:98`.
    NoCtors { ty: ExprId },
    /// `:99-100`.
    MultipleCtors { ty: ExprId },
    /// `:77-82`. The oracle logs this under `errToSorry` and pads with
    /// labeled `sorry`s; leanr has no `errToSorry` and throws.
    InsufficientFields {
        ctor: String,
        explicit: usize,
        provided: usize,
    },
    /// `:89-91`.
    NoExplicitFields { ctor: String, provided: usize },
}
```

Open `BuiltinNotation.lean` and confirm each line number before saving. `is_oracle_error` needs no change, because the new variant is not in its exclusion list, which is correct: these are all `throwError`s. In `crates/leanr_elab/src/lib.rs:262`, add `AnonCtorError` to the `pub use error::{…}` list.

- [ ] **Step 8: Widen the three `lval.rs` helpers.** In `crates/leanr_elab/src/app/lval.rs`, change `pub(super) fn node`, `pub(super) fn app_fn` and `pub(super) fn render` (lines 74, 79, 97) to `pub(crate)`. They take no other change.

- [ ] **Step 9: Write the elaborator.** Create `crates/leanr_elab/src/builtin/anon_ctor.rs`:

```rust
//! The anonymous constructor `⟨…⟩`. Oracle: `elabAnonymousCtor`
//! (`Lean/Elab/BuiltinNotation.lean:43-102`). Design spec:
//! `docs/superpowers/specs/2026-09-30-m4b4b-anonymous-constructor-design.md`.
//!
//! The oracle builds new syntax — `$(mkCIdentFrom stx ctor (canonical :=
//! true)) $(args)*` — and elaborates it. leanr calls the application
//! elaborator on the constructor directly: `mkCIdentFrom` carries a
//! reserved macro scope and `[.decl ctor []]` (`Init/Meta/Defs.lean:736-739`),
//! so `resolveName`'s `resolveLocalName` (`TermElabM.lean:2180`) can never
//! capture it and the preresolved decl becomes `mkConst` with fresh level
//! mvars — `mk_const(ctor, &[])`. `withMacroExpansion` (`:97`) has no
//! counterpart: leanr has no macro stack.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_kernel::{BinderInfo, ConstantInfo};
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::{NodeOrToken, SyntaxNode};

use crate::app::expand::Arg;
use crate::app::head::mk_const;
use crate::app::lval::{app_fn, node as expr_node, render};
use crate::app::AppCall;
use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::TermElabM;
use crate::error::{AnonCtorError, ElabError};

/// The term arguments of an `anonymousCtor` node, `,` separators
/// dropped. Shape: `⟨` atom, a `null` node holding `arg (, arg)*`, `⟩`
/// atom (confirmed by `anon_ctor_smoke.rs`'s shape probe).
pub(crate) fn anon_ctor_args(
    node: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<Vec<SynElem>, ElabError> {
    let children = non_trivia_children(node);
    let list = match children.as_slice() {
        [_, NodeOrToken::Node(list), _] => list.clone(),
        _ => {
            return Err(ElabError::IllFormedSyntax(format!(
                "anonymousCtor: expected `⟨`, an argument list and `⟩`, got {} children",
                children.len()
            )))
        }
    };
    Ok(non_trivia_children(&list)
        .into_iter()
        .filter(|el| {
            !(kinds.name(el.kind()) == "<atom>"
                && el.as_token().is_some_and(|t| t.text() == ","))
        })
        .collect())
}

/// oracle: `elabAnonymousCtor` (`BuiltinNotation.lean:43-102`), over
/// `args[from..]` of `node`. `from` is 0 for a real `⟨…⟩`; the flatten
/// tail (Task 2) re-enters with a later start on the SAME node, which is
/// the oracle's recursion through its synthesized `⟨$[$extra],*⟩`.
pub(crate) fn elab_anon_ctor(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    from: usize,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let all = anon_ctor_args(node, kinds)?;
    let Some(args) = all.get(from..) else {
        return Err(ElabError::Internal(format!(
            "anonymousCtor tail starts at {from}, past its {} arguments",
            all.len()
        )));
    };
    let unknown = || ElabError::InvalidAnonymousCtor(AnonCtorError::ExpectedTypeUnknown);
    // `:46`.
    elab.try_postpone_if_none_or_mvar(expected)?;
    // `:101`.
    let Some(expected) = expected else {
        return Err(unknown());
    };
    // `:53-54`: default-transparency `whnf`; an mvar head is a hard
    // error here, not a second postponement.
    let ty = elab.mctx.whnf(expected)?;
    let head = expr_node(elab, app_fn(elab, ty));
    if matches!(head, Node::MVar { .. }) {
        return Err(unknown());
    }
    // `:55-57`: `matchConstInduct`.
    let ctors = match head {
        Node::Const { name: Some(c), .. } => match elab.view.get(c) {
            Some(ConstantInfo::Induct(ind)) => Some(ind.ctors.clone()),
            _ => None,
        },
        _ => None,
    };
    let Some(ctors) = ctors else {
        return Err(ElabError::InvalidAnonymousCtor(AnonCtorError::NotInductive { ty }));
    };
    // `:59`, `:98-99`.
    let ctor = match ctors.as_slice() {
        [c] => *c,
        [] => return Err(ElabError::InvalidAnonymousCtor(AnonCtorError::NoCtors { ty })),
        _ => {
            return Err(ElabError::InvalidAnonymousCtor(AnonCtorError::MultipleCtors { ty }))
        }
    };
    let ctor_name = render(elab, ctor);
    // `:61-62` `isInaccessiblePrivateName`: leanr models no private
    // names (the same seam as `app/lval.rs` and `app/dot_ident.rs`).
    if ctor_name.starts_with("_private.") {
        return Err(ElabError::UnsupportedSyntax(format!(
            "`⟨…⟩` with the private constructor `{ctor_name}` (`isInaccessiblePrivateName`, \
             BuiltinNotation.lean:61) — the slice that models private names"
        )));
    }
    // `:63` `getConstInfoCtor`.
    let ctor_info = match elab.view.get(ctor) {
        Some(ConstantInfo::Ctor(c)) => c.num_params.to_usize().map(|p| (c.val.ty, p)),
        _ => None,
    };
    let Some((ctor_ty, num_params)) = ctor_info else {
        return Err(ElabError::Internal(format!(
            "`{ctor_name}` is not a constructor with a machine-sized `numParams` \
             (getConstInfoCtor, BuiltinNotation.lean:63)"
        )));
    };
    // `:64-69`.
    let k = num_explicit_fields(elab, ctor_ty, num_params)?;
    let n = args.len();
    // `:71-96`, in the oracle's order.
    let app_args: Vec<Arg> = if n < k {
        return Err(ElabError::InvalidAnonymousCtor(AnonCtorError::InsufficientFields {
            ctor: ctor_name,
            explicit: k,
            provided: n,
        }));
    } else if n == k {
        args.iter().cloned().map(Arg::Stx).collect()
    } else if k == 0 {
        return Err(ElabError::InvalidAnonymousCtor(AnonCtorError::NoExplicitFields {
            ctor: ctor_name,
            provided: n,
        }));
    } else {
        return Err(ElabError::UnsupportedSyntax(
            "`⟨…⟩` with more arguments than explicit fields (flattening) — M4b-4b task 2"
                .to_string(),
        ));
    };
    // `:97`: `elabTerm newStx expectedType?` — the ORIGINAL expected
    // type, not its `whnf`.
    let f = mk_const(elab, ctor, &[], &ctor_name)?;
    crate::app::elab_app_args(
        elab,
        f,
        AppCall {
            named_args: Vec::new(),
            args: app_args,
            expected: Some(expected),
            explicit: false,
            ellipsis: false,
            stx: NodeOrToken::Node(node.clone()),
        },
        kinds,
    )
}

/// oracle: `:64-69` — `forallTelescopeReducing cinfo.type`, counting the
/// explicit (`BinderInfo::Default`) binders at positions
/// `numParams..`. The walk is `AppElab::forall_telescope_reducing`'s
/// (`app/state.rs`), inlined because there is no `AppElab` here; the
/// ambient `lctx` is restored on every exit path.
fn num_explicit_fields(
    elab: &mut TermElabM,
    ctor_ty: ExprId,
    num_params: usize,
) -> Result<usize, ElabError> {
    let checkpoint = elab.mctx.lctx_checkpoint();
    let result = (|| {
        let mut count = 0;
        let mut i = 0;
        let mut cur = ctor_ty;
        loop {
            let reduced = if matches!(expr_node(elab, cur), Node::Forall { .. }) {
                cur
            } else {
                elab.mctx.whnf(cur)?
            };
            let Node::Forall {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = expr_node(elab, reduced)
            else {
                break;
            };
            if i >= num_params && binder_info == BinderInfo::Default {
                count += 1;
            }
            let fvar = elab.mctx.push_local_decl(binder_name, binder_type, binder_info)?;
            cur = elab.mctx.instantiate_beta_rev_range(body, &[fvar])?;
            i += 1;
        }
        Ok(count)
    })();
    elab.mctx.lctx_restore(checkpoint);
    result
}
```

If `elab_app_args` is not reachable as `crate::app::elab_app_args` (it is `pub(crate)` in `app/mod.rs:480`), fix the path. Do not widen anything else. Compile errors on `Node` field names or `push_local_decl`'s `binder_name` type should be fixed by matching `app/state.rs:545-600`, which is the same walk.

- [ ] **Step 10: Register and route the kind.**
- In `crates/leanr_elab/src/builtin/mod.rs`, add `pub mod anon_ctor;` in alphabetical order.
- In `crates/leanr_elab/src/dispatch.rs`'s `elaborator_name_for`, add `"Lean.Parser.Term.anonymousCtor" => Some("anonymousCtor"),` after the `dotIdent` arm.
- In `dispatch`, add this after the `namedPattern` arm:

```rust
        // oracle: `@[builtin_term_elab anonymousCtor] elabAnonymousCtor`
        // (`BuiltinNotation.lean:43-102`).
        ("Lean.Parser.Term.anonymousCtor", NodeOrToken::Node(node)) => {
            crate::builtin::anon_ctor::elab_anon_ctor(elab, node, 0, kinds, expected)
        }
```

- In `dispatch`'s doc comment deferred list (`dispatch.rs:179`), change the `anonymous constructor ⟨⟩ … M4b-4b` row to `anonymous constructor ⟨⟩ (term position) ...... M4b-4b SHIPPED — builtin/anon_ctor.rs; pattern position: the match slice`.
- In `src/lib.rs:139`, change the sentence naming `⟨⟩` as M4b-4b's deferral so that it says `⟨⟩` is elaborated by `builtin::anon_ctor` (M4b-4b), with the pattern position left to the match slice.

- [ ] **Step 11: Add the argument-shape probe to the smoke file.** Append to `anon_ctor_smoke.rs`. This pins the separator filter against the real parse, including trivia:

```rust
/// `anon_ctor_args`'s shape assumption, checked end to end: separators,
/// comments and whitespace are not arguments. The oracle elaborates the
/// trivia form to `@Prod.mk … Nat.zero Nat.zero` (corpus `anon/trivia`);
/// a wrong filter shows up here as InsufficientFields or a type mismatch.
#[test]
fn separators_and_trivia_are_not_arguments() {
    support::elab_and_synthesize("(⟨Nat.zero /- c -/ ,   Nat.zero⟩ : Prod Nat Nat)")
        .expect("two arguments");
    support::elab_and_synthesize("(⟨⟩ : PUnit)").expect("zero arguments");
}
```

- [ ] **Step 12: Run the tests and verify they pass.**

Run: `cargo test -p leanr_elab --test anon_ctor_smoke --test oracle_elab 2>&1 | tail -20`
Expected: PASS, with all 12 `anon/*` records identical to the oracle.

`seam_audit`'s `unregistered_kinds_are_named_by_kind` now FAILS, because the kind is registered. That is expected. Task 3 rewrites that test, but for this commit delete only its `("⟨Nat.zero, Nat.zero⟩", "Lean.Parser.Term.anonymousCtor")` case line and the three-line `// M4b-4b: …` comment above it. Task 3 then replaces the emptied test.

Then run: `cargo test -p leanr_elab 2>&1 | grep -E '^test result|FAILED|panicked' | head -40`
Expected: every binary reports `ok`.

- [ ] **Step 13: Kill check.** Do this before committing, and keep none of the edits. Apply each mutation, run `cargo test -p leanr_elab --test anon_ctor_smoke --test oracle_elab`, see it go red, then revert it with `git checkout -p` or by editing back:
  - In `num_explicit_fields`, drop `i >= num_params &&`. `eq_counts_fields_after_its_promoted_parameters` must fail.
  - Drop `&& binder_info == BinderInfo::Default`. `anon/implicitField` must fail.
  - Replace `elab.mctx.whnf(expected)?` with `expected`. `anon/unitAlias` must fail.
  - Move the `k == 0` branch ahead of `n < k` and `n == k`. `anon/punit` must fail: `(⟨⟩ : PUnit)` has n = k = 0, and it must reach the `n == k` success, not `NoExplicitFields`. The spec's mutation table credits this kill to the `True`/`Prod` smoke tests. That is wrong, so record the correction in Task 3's `## Landed`.

- [ ] **Step 14: Format, lint, commit.**

```bash
cd /workspace && cargo fmt --all && cargo clippy -p leanr_elab --all-targets -- -D warnings 2>&1 | tail -3
git add tests/fixtures/elab crates/leanr_elab
git commit -m "M4b-4b task 1: anonymous constructor, exact arity"
```

---

### Task 2: The flatten tail through `Arg` and postponement

**Files:**
- Modify: `crates/leanr_elab/src/elab.rs` (`elab_term`, `elab_term_without_implicit_lambda`, `resume_elab_term`, `elab_term_core`, `elab_using_elab_fns`, `use_implicit_lambda` call site, `elab_implicit_lambda`)
- Modify: `crates/leanr_elab/src/postpone.rs:77-90`
- Modify: `crates/leanr_elab/src/synthetic/state.rs:70-75`, `synthetic/ladder.rs:151-153`, `:456-475`
- Modify: `crates/leanr_elab/src/app/expand.rs:77-80`, `app/propagate.rs:31-41`, `app/args.rs:953`, `:1037-1044`
- Modify: `crates/leanr_elab/src/builtin/anon_ctor.rs` (the flatten branch)
- Modify: `tests/fixtures/elab/dump_elab.lean`; regenerate `elab-queries.jsonl`
- Modify: `crates/leanr_elab/tests/anon_ctor_smoke.rs`

**Interfaces:**
- Consumes: `elab_anon_ctor(elab, node, from, kinds, expected)` from Task 1.
- Produces:
  - `pub(crate) fn postpone_elab_target(&mut self, target: &TermTarget, expected: Option<ExprId>)` in `postpone.rs`. The public `postpone_elab_term(&SynElem, …)` stays as a wrapper.
  - `pub(crate) enum TermTarget { Stx(SynElem), AnonCtorTail { node: SyntaxNode, from: usize } }` in `crate::elab`, with `fn ref_elem(&self) -> SynElem`, `fn tail_from(&self) -> Option<usize>` and `fn from_parts(stx: &SynElem, tail_from: Option<usize>) -> Result<TermTarget, ElabError>`
  - `TermElabM::elab_target(&mut self, t: &TermTarget, kinds, expected: Option<ExprId>)` and `TermElabM::resume_elab_target(&mut self, t: &TermTarget, kinds, expected: ExprId)`, both `pub(crate)`
  - `Arg::AnonCtorTail { node: SyntaxNode, from: usize }`
  - `SyntheticMVarKind::Postponed { ctx: SavedContext, tail_from: Option<usize> }`

- [ ] **Step 1: Add the Task 2 corpus queries.** In `dump_elab.lean`, add this after `anonQueries`, and append `++ anonTailQueries` to `main`'s concatenation:

```lean
-- M4b-4b task 2: flattening (`BuiltinNotation.lean:92-96`), including a
-- tail that postpones on `?β` and resumes as the tail
-- (`anon/tailPostponed`), and the same under a binder whose fvar the
-- resumed tail must see through its saved context.
def anonTailQueries : List (String × String) :=
  [ ("anon/flat1",            "(⟨Nat.zero, Nat.zero, Nat.zero⟩ : Prod Nat (Prod Nat Nat))")
  , ("anon/flat2",            "(⟨Nat.zero, Nat.zero, Nat.zero, Nat.zero⟩ : Prod Nat (Prod Nat (Prod Nat Nat)))")
  , ("anon/tailPostponed",    "sameAs (⟨Nat.zero, Nat.zero, Nat.zero⟩ : Prod Nat _) (Prod.mk Nat.zero (Prod.mk Nat.zero Nat.zero))")
  , ("anon/tailUnderBinder",  "fun (n : Nat) => sameAs (⟨n, n, n⟩ : Prod Nat _) (Prod.mk n (Prod.mk n n))")
  ]
```

Run:
```bash
cd /workspace && mise run fixtures:regen-elab 2>&1 | tail -3
grep -c '"id":"anon/' tests/fixtures/elab/elab-queries.jsonl
git diff --stat tests/fixtures/elab/elab-queries.jsonl
```
Expected: `16` records, and `elab-queries.jsonl` has 4 added lines and no other changes.

- [ ] **Step 2: Add the failing smoke tests.** Append to `anon_ctor_smoke.rs`:

```rust
#[test]
fn insufficient_fields_in_the_nested_tail() {
    // "Insufficient number of fields for `⟨...⟩` constructor: Constructor
    // `T3.mk` has 3 explicit field, but only 2 were provided" — raised by
    // the synthesized tail `⟨Nat.zero, Nat.zero⟩ : T3`.
    assert_eq!(
        anon_err("(⟨Nat.zero, Nat.zero, Nat.zero⟩ : Prod Nat T3)"),
        AnonCtorError::InsufficientFields {
            ctor: "T3.mk".to_string(),
            explicit: 3,
            provided: 2
        }
    );
}

#[test]
fn a_tail_whose_type_never_resolves_reports_expected_type_unknown() {
    // "Invalid `⟨...⟩` notation: The expected type of this term could not
    // be determined", at the OUTER `⟨` column: the tail postponed on
    // `?β`, nothing solved it, and the final resume runs with
    // postponement off.
    assert_eq!(
        anon_err("(⟨Nat.zero, Nat.zero, Nat.zero⟩ : Prod Nat _)"),
        AnonCtorError::ExpectedTypeUnknown
    );
}

/// Review Focus 2: an error inside a RESUMED tail is the oracle's error,
/// not swallowed and not a seam. Oracle: "Invalid `⟨...⟩` notation: The
/// expected type `(x : Nat) → Nat` is not an inductive type".
#[test]
fn a_resumed_tail_reports_its_own_error() {
    assert!(matches!(
        anon_err(
            "sameAs (⟨Nat.zero, Nat.zero, Nat.zero⟩ : Prod Nat _) \
             (Prod.mk Nat.zero (fun x : Nat => x))"
        ),
        AnonCtorError::NotInductive { .. }
    ));
}
```

Run: `cargo test -p leanr_elab --test anon_ctor_smoke --test oracle_elab 2>&1 | tail -20`
Expected: FAIL. The four new records and three new smoke tests hit the `M4b-4b task 2` flattening seam.

- [ ] **Step 3: Add `TermTarget` to `elab.rs`.** Put it above `impl<'e> TermElabM<'e>` (or at the top of the file after the `use`s, following local convention), and add `use leanr_syntax::tree::{NodeOrToken, SyntaxNode};` if either name isn't imported yet:

```rust
/// What `elab_term_core` elaborates: a real syntax element, or the
/// anonymous constructor's flatten TAIL — `args[from..]` of the outer
/// `⟨…⟩` node, the oracle's synthesized `⟨$[$extra],*⟩`
/// (`BuiltinNotation.lean:93-96`). The tail's ref is the outer node: the
/// synthesized node has kind `anonymousCtor` and `SourceInfo.fromRef` the
/// outer node, so implicit-lambda blocking, postponement refs, and
/// `report.rs`'s range ordering all see what the oracle's see (design
/// spec 2026-09-30-m4b4b § The tail form). The macro-expansion slice's
/// synthesized syntax grows here.
#[derive(Debug, Clone)]
pub(crate) enum TermTarget {
    Stx(SynElem),
    AnonCtorTail { node: SyntaxNode, from: usize },
}

impl TermTarget {
    pub(crate) fn ref_elem(&self) -> SynElem {
        match self {
            TermTarget::Stx(e) => e.clone(),
            TermTarget::AnonCtorTail { node, .. } => NodeOrToken::Node(node.clone()),
        }
    }

    pub(crate) fn tail_from(&self) -> Option<usize> {
        match self {
            TermTarget::Stx(_) => None,
            TermTarget::AnonCtorTail { from, .. } => Some(*from),
        }
    }

    /// Rebuild a target from a postponed mvar's `(stx, tail_from)`.
    pub(crate) fn from_parts(stx: &SynElem, tail_from: Option<usize>) -> Result<Self, ElabError> {
        match (tail_from, stx) {
            (None, _) => Ok(TermTarget::Stx(stx.clone())),
            (Some(from), NodeOrToken::Node(node)) => Ok(TermTarget::AnonCtorTail {
                node: node.clone(),
                from,
            }),
            (Some(_), NodeOrToken::Token(_)) => Err(ElabError::Internal(
                "a postponed anonymous-constructor tail whose ref is a token".to_string(),
            )),
        }
    }
}
```

- [ ] **Step 4: Thread `TermTarget` through `elab_term_core`.** In `elab.rs`:
  - `elab_term` and `elab_term_without_implicit_lambda` keep their `&SynElem` signatures and bodies, except that each passes `&TermTarget::Stx(elem.clone())` to `elab_term_core`.
  - Delete `resume_elab_term` (`pub(crate)`, whose only caller is `ladder.rs:474`, rewritten in Step 5). An unused copy fails clippy's `dead_code`. Move its doc comment (the `resumeElabTerm` oracle citation and the `errToSorry` note) onto `resume_elab_target` below.
  - Add, next to them:

```rust
    /// `elab_term` over a [`TermTarget`] — the anonymous constructor's
    /// flatten tail (`app/args.rs`'s `elab_and_add_new_arg`).
    pub(crate) fn elab_target(
        &mut self,
        target: &TermTarget,
        kinds: &KindInterner,
        expected: Option<ExprId>,
    ) -> Result<ExprId, ElabError> {
        self.elab_term_core(target, kinds, expected, true, true)
    }

    /// `resume_elab_term` over a [`TermTarget`] (`resume_postponed`).
    pub(crate) fn resume_elab_target(
        &mut self,
        target: &TermTarget,
        kinds: &KindInterner,
        expected: ExprId,
    ) -> Result<ExprId, ElabError> {
        self.elab_term_core(target, kinds, Some(expected), false, true)
    }
```

  - `elab_term_core(&mut self, target: &TermTarget, …)`:
    - In the `!implicit_lambda` branch, the paren-stripping loop applies only to `TermTarget::Stx`. Match first: for `Stx(elem)`, run the existing loop and call `self.elab_using_elab_fns(&TermTarget::Stx(cur), …)`. For a tail, call `self.elab_using_elab_fns(target, …)` directly.
    - Everywhere else, pass `&target.ref_elem()` to `use_implicit_lambda`.
    - Pass `target` to `elab_implicit_lambda` and `elab_using_elab_fns`, and call `postpone_elab_target(target, …)` (Step 5) where it called `postpone_elab_term`.
  - `elab_using_elab_fns(&mut self, target: &TermTarget, …)`: replace both `dispatch::dispatch(self, elem, kinds, expected)` calls with `self.dispatch_target(target, kinds, expected)`, call `postpone_elab_target(target, …)`, and add:

```rust
    fn dispatch_target(
        &mut self,
        target: &TermTarget,
        kinds: &KindInterner,
        expected: Option<ExprId>,
    ) -> Result<ExprId, ElabError> {
        match target {
            TermTarget::Stx(elem) => dispatch::dispatch(self, elem, kinds, expected),
            TermTarget::AnonCtorTail { node, from } => {
                crate::builtin::anon_ctor::elab_anon_ctor(self, node, *from, kinds, expected)
            }
        }
    }
```

  - `elab_implicit_lambda(elab, target: &TermTarget, …)`: its body calls `elab.elab_using_elab_fns(target, kinds, Some(ty), catch_ex_postpone)?` and `elab.ensure_has_type(&target.ref_elem(), Some(ty), body)?`.

- [ ] **Step 5: Record `tail_from` on postponement.**
  - In `synthetic/state.rs:74`, change the variant to:

```rust
    /// `tail_from` is `Some(i)` when the postponed term is an anonymous
    /// constructor's flatten tail (`args[i..]` of the node in the decl's
    /// `stx`), so the resume re-enters the TAIL, not the whole `⟨…⟩`
    /// (`elab.rs`'s `TermTarget`).
    Postponed { ctx: SavedContext, tail_from: Option<usize> },
```

  - In `postpone.rs`, keep `pub fn postpone_elab_term(&mut self, stx: &SynElem, expected)` unchanged in signature, because `tests/postpone_smoke.rs` calls it and a `pub` fn cannot take the `pub(crate)` `TermTarget` (clippy's `private_interfaces`). Move its body into a new `pub(crate) fn postpone_elab_target(&mut self, target: &crate::elab::TermTarget, expected: Option<ExprId>) -> Result<ExprId, ElabError>`, and make `postpone_elab_term` a one-line `self.postpone_elab_target(&TermTarget::Stx(stx.clone()), expected)`. In `postpone_elab_target`, the registration line becomes:

```rust
        self.register_synthetic_mvar(
            target.ref_elem(),
            mvar_id,
            SyntheticMVarKind::Postponed {
                ctx,
                tail_from: target.tail_from(),
            },
        );
```

    In `elab.rs`, the three `self.postpone_elab_term(elem, expected)` calls in `elab_term_core` / `elab_using_elab_fns` become `self.postpone_elab_target(target, expected)`.
  - In `synthetic/ladder.rs:151`, change the arm to `SyntheticMVarKind::Postponed { ref ctx, tail_from } => elab.resume_postponed(ctx, &decl.stx, tail_from, mvar_id, postpone_on_error, kinds)`. In `resume_postponed`, add the parameter `tail_from: Option<usize>` after `stx`, and replace `let e = elab.resume_elab_term(&stx, kinds, expected)?;` with:

```rust
            let target = crate::elab::TermTarget::from_parts(&stx, tail_from)?;
            let e = elab.resume_elab_target(&target, kinds, expected)?;
```

    The following `ensure_has_type(&stx, …)` stays as it is, because `stx` is already the outer node.

- [ ] **Step 6: Add the `Arg` variant and its match arms.**
  - In `app/expand.rs:77`:

```rust
pub enum Arg {
    Stx(SynElem),
    Expr(ExprId),
    /// The anonymous constructor's flatten tail: `args[from..]` of the
    /// `anonymousCtor` `node`, the oracle's synthesized
    /// `⟨$[$extra],*⟩` (`BuiltinNotation.lean:93-96`). Elaborated through
    /// `elab.rs`'s `TermTarget::AnonCtorTail`.
    AnonCtorTail { node: SyntaxNode, from: usize },
}
```

    `SyntaxNode` is already imported there.
  - In `app/propagate.rs`'s `should_propagate_expected_type_for`, add the arm `Arg::AnonCtorTail { .. } => true,`, with a comment that the synthesized node's kind is `anonymousCtor`, which is not one of the three excluded kinds (`App.lean:516-523`).
  - `app/args.rs:953` (`next_arg_hole`) already returns `None` for anything that isn't `Arg::Stx`, so it needs no change. Confirm that by reading it.
  - In `app/args.rs:1037-1044`:

```rust
    let stx = match &arg {
        Arg::Stx(elem) => elem.clone(),
        Arg::AnonCtorTail { node, .. } => NodeOrToken::Node(node.clone()),
        Arg::Expr(_) => app.ctx.stx.clone(),
    };
    let val = match arg {
        Arg::Expr(e) => e,
        Arg::Stx(elem) => app.elab.elab_term(&elem, kinds, Some(expected))?,
        Arg::AnonCtorTail { node, from } => app.elab.elab_target(
            &crate::elab::TermTarget::AnonCtorTail { node, from },
            kinds,
            Some(expected),
        )?,
    };
```

    Import `NodeOrToken` from `leanr_syntax::tree` if it isn't imported already. Build with `cargo build -p leanr_elab 2>&1 | grep -E '^(error|warning)' -A5`. Any other non-exhaustive `match` on `Arg` that the compiler reports gets the arm that treats the tail as unelaborated syntax. Mirror the `Arg::Stx` arm and write a comment explaining why.

- [ ] **Step 7: Replace the flattening seam.** In `builtin/anon_ctor.rs`, replace the final `else { return Err(ElabError::UnsupportedSyntax(… task 2 …)) }` branch with:

```rust
    } else {
        // `:93-96`: the first `k - 1` arguments stay, the rest become
        // one nested `⟨…⟩` — the same node, a later start.
        let mut v: Vec<Arg> = args[..k - 1].iter().cloned().map(Arg::Stx).collect();
        v.push(Arg::AnonCtorTail {
            node: node.clone(),
            from: from + k - 1,
        });
        v
    };
```

- [ ] **Step 8: Run the tests and verify they pass.**

Run: `cargo test -p leanr_elab --test anon_ctor_smoke --test oracle_elab --test postpone_smoke 2>&1 | tail -20`
Expected: PASS. All 16 `anon/*` records match, and so do all smoke tests.

Then run: `cargo test -p leanr_elab 2>&1 | grep -E '^test result|FAILED|panicked'`
Expected: all `ok`. `oracle_elab`'s leaked-fvar assertion must stay green for `anon/tailUnderBinder`.

- [ ] **Step 9: Kill check.** Keep none of these edits. Apply each mutation, run `cargo test -p leanr_elab --test anon_ctor_smoke --test oracle_elab`, confirm it goes red, and revert:
  - `from + k - 1` → `from + k`. `anon/flat1` must fail.
  - In `ladder.rs`, pass `None` instead of `tail_from` to `from_parts`, so the resume elaborates the whole node. `anon/tailPostponed` must fail.
  - In `anon_ctor.rs`, push `from` (not `from + k - 1`) as the tail's start, so the recursion doesn't advance. `anon/flat2` and `anon/flat1` must fail.
  - In `TermTarget::ref_elem`, this has no mutation, because the tail's ref has only one sensible value.

If any mutation survives, add a test that kills it before committing. Don't record a surviving mutation as acceptable unless you can argue it is equivalent.

- [ ] **Step 10: Format, lint, commit.**

```bash
cd /workspace && cargo fmt --all && cargo clippy -p leanr_elab --all-targets -- -D warnings 2>&1 | tail -3
git add tests/fixtures/elab crates/leanr_elab
git commit -m "M4b-4b task 2: the flatten tail through Arg and postponement"
```

---

### Task 3: Seam audit, pattern-position pin, landed notes, CI

**Files:**
- Modify: `crates/leanr_elab/tests/seam_audit.rs` (`unregistered_kinds_are_named_by_kind` at `:285-322`, `no_seam_message_names_a_completed_slice` at `:772-800`)
- Modify: `crates/leanr_elab/tests/anon_ctor_smoke.rs`
- Modify: `docs/superpowers/specs/2026-09-30-m4b4b-anonymous-constructor-design.md` (append `## Landed`)

**Interfaces:**
- Consumes: everything above. Produces nothing new.

- [ ] **Step 1: Probe the pattern-position form.** Append a temporary test to `anon_ctor_smoke.rs` that prints `support::elab_and_synthesize("fun ⟨a, b⟩ => a")` with `{:?}`, and run it with `-- --nocapture`. Record the exact `Err(UnsupportedSyntax(msg))`. The expected form is `fun: unsupported binder kind …`, raised by `builtin/binder/fun.rs:249-257`. **If it is anything other than an `UnsupportedSyntax`**, and in particular if it reaches `InvalidAnonymousCtor`, stop and report it: the term elaborator is being reached from a pattern position, and that is a design problem, not something to paper over with a test. The oracle's answer for `fun ⟨a, b⟩ => (a : Nat)` is its matcher's "expected type … could not be determined".

- [ ] **Step 2: Replace the probe with the pin.** Replace the temporary test with:

```rust
/// `⟨⟩` in a pattern position belongs to the match slice (later M4):
/// `fun ⟨a, b⟩ => …` expands to a `match` in the oracle and never reaches
/// the term elaborator. leanr must keep it a named seam, never route it
/// through `builtin::anon_ctor`.
#[test]
fn pattern_position_anonymous_constructor_stays_a_seam() {
    match support::elab_and_synthesize("fun ⟨a, b⟩ => a") {
        Err(ElabError::UnsupportedSyntax(m)) => {
            assert!(m.contains("unsupported binder kind"), "{m}")
        }
        other => panic!("expected the pattern-position seam, got {other:?}"),
    }
}
```

If Step 1 recorded a different `UnsupportedSyntax` message, change the `contains` needle to a stable substring of that message. The needle must not be the whole message, which contains the kind name that `leanr_syntax` may rename.

- [ ] **Step 3: Rewrite `unregistered_kinds_are_named_by_kind`.** After Task 1 its case list is empty, which makes the test vacuous. First probe whether `Lean.Parser.Term.match` is still unregistered and parses:

```bash
cd /workspace && grep -n '"Lean.Parser.Term.match"' crates/leanr_elab/src/dispatch.rs
```

If that prints nothing (the kind is unregistered), set the case list to `("match Nat.zero with | x => x", "Lean.Parser.Term.match")`, update the comment to say that `match` belongs to the match slice and that `anonymousCtor` has been registered since M4b-4b, and run `cargo test -p leanr_elab --test seam_audit unregistered_kinds_are_named_by_kind`.
- If it passes, keep it.
- If the source does not parse with `leanr_syntax`'s grammar, or the seam's message is not the bare kind name, delete the test and leave a comment in its place saying that no parseable unregistered term kind remains to pin, and that `dispatch`'s catch-all is still covered by `dispatch.rs`'s own doc audit. Say which of these outcomes happened in your report.

Then add a registration check next to it:

```rust
#[test]
fn anonymous_constructor_is_registered() {
    assert_eq!(
        leanr_elab::dispatch::elaborator_name_for("Lean.Parser.Term.anonymousCtor"),
        Some("anonymousCtor")
    );
}
```

- [ ] **Step 4: Add the `M4b-4b` needle.** In `no_seam_message_names_a_completed_slice`, add `"M4b-4b",` to `needles`, and change the assertion message to `"M4b-3 P3, P4, P5, M4b-4a P1–P4 and M4b-4b are complete; …"`. Then run the non-vacuity check: temporarily restore the Task 1 flattening seam string (`"… — M4b-4b task 2"`) in live code, confirm the test fails, and revert.

Run: `cargo test -p leanr_elab --test seam_audit 2>&1 | tail -5`
Expected: PASS once the temporary seam string is reverted.

- [ ] **Step 5: Sweep the citations.** Run `grep -rn "BuiltinNotation.lean:" crates/leanr_elab/src crates/leanr_elab/tests` and open every cited line in `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/Lean/Elab/BuiltinNotation.lean`. Fix any citation that is off. Do the same for `Init/Meta/Defs.lean:736` and `TermElabM.lean:2180`.

- [ ] **Step 6: Append `## Landed` to the spec.** Add it at the end of `docs/superpowers/specs/2026-09-30-m4b4b-anonymous-constructor-design.md`:
- the PR number (fill it in after the PR is opened, in the same PR)
- the corpus delta (+16 `anon/*` records, so the total goes to 292; get the exact number from `wc -l tests/fixtures/elab/elab-queries.jsonl`)
- the mutation results from Task 1 step 13 and Task 2 step 9, including any mutation shown to be equivalent
- the outcome of Task 3 step 3
- the seams left open: pattern position (match slice), private names, the `errToSorry` narrowing, and `TermTarget` as the growth point for the macro-expansion slice

- [ ] **Step 7: Run full CI in the foreground.**

Run: `cd /workspace && mise run ci; echo CI_EXIT=$?`
Expected: `CI_EXIT=0`. Block on it. Do not background it.

- [ ] **Step 8: Commit.**

```bash
cd /workspace && cargo fmt --all
git add crates/leanr_elab docs/superpowers/specs/2026-09-30-m4b4b-anonymous-constructor-design.md
git commit -m "M4b-4b task 3: seam audit, pattern-position pin, landed notes"
```
