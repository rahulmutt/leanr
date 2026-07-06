# Expr hash-consing (batch canonicalization) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Cut the whole-stdlib `leanr check --all` peak memory from ≥31 GiB to comfortably under 32 GiB by structurally interning (hash-consing) decoded expressions in a single batch pass before replay, with zero change to any accept/reject verdict.

**Architecture:** A new `leanr_kernel::intern` module provides a **transient** `Interner` (a bucketed hash-cons table over `Expr` and `Level`, plus input-pointer memos). A bottom-up, `RecGuard`-guarded pass canonicalizes every expression reachable from each decoded `ConstantInfo`; structurally-identical subterms across all 2433 modules collapse to one shared `Arc`. The interner is built, used to rewrite the decoded constants, then dropped — the dedup is baked into the resulting `Arc` graph, which the `Environment` inherits during replay. The CLI `check` path runs this pass after decode and before replay. No global state, no `Weak` refs, no hot-path cost.

**Tech Stack:** Rust (mise-pinned 1.96.0), the existing `leanr_kernel` primitives (`Expr`/`ExprNode`, `Level`, `RecGuard`, `ConstantInfo`), `std::collections::HashMap`. No new dependencies.

## Global Constraints

- `leanr_kernel` depends on **no workspace crate** (TCB rule, AGENTS.md). No new external deps of any kind in this plan.
- `.olean`-derived values are untrusted: **no panic, no unguarded recursion, no unbounded allocation not tied to input length.** All recursion over `Expr`/`Level` goes through `RecGuard::enter` (returns `KernelError::DeepRecursion` at the `MAX_REC_DEPTH = 1_000_000` cap), never native recursion.
- **Verdict preservation is the hard invariant.** Interning may only merge exprs that are identical in *every* field. The full `cargo test --workspace` suite — especially `crates/leanr_olean/tests/check_fixtures.rs` (real replay + hermetic mutation-differential verdicts) — must stay green. Any verdict drift is a defect, not an accepted cost.
- Checked arithmetic on anything derived from olean values (M1a rule). The `Nat` index fields are compared, not arithmetic'd, here.
- Lint gate before every commit: `mise run lint` (`cargo fmt --all --check` + `cargo clippy --workspace --all-targets -- -D warnings`).
- Conventional-commit prefixes (`feat:`, `perf:`, `test:`, `docs:`).
- Spec: `docs/superpowers/specs/2026-07-06-expr-hash-consing-design.md`.

## Key facts about the existing code (verified, cite in comments)

- `Expr` (crates/leanr_kernel/src/expr.rs): `pub fn node(&self) -> &ExprNode`, `pub fn data(&self) -> ExprData`; `ExprData::hash(self) -> u32` is a structural hash (`structural_eq ⇒ equal hashes`). Smart constructors: `Expr::bvar(Nat)`, `fvar(Arc<Name>)`, `mvar(Arc<Name>)`, `sort(Arc<Level>, &mut RecGuard) -> Result<Arc<Expr>, KernelError>`, `const_(Arc<Name>, Vec<Arc<Level>>, &mut RecGuard) -> Result<…>`, `app(Arc<Expr>, Arc<Expr>) -> Arc<Expr>`, `lam(Arc<Name>, Arc<Expr>, Arc<Expr>, BinderInfo)`, `forall_e(Arc<Name>, Arc<Expr>, Arc<Expr>, BinderInfo)`, `let_e(Arc<Name>, Arc<Expr>, Arc<Expr>, Arc<Expr>, bool)`, `lit(Literal)`, `mdata(KVMap, Arc<Expr>)`, `proj(Arc<Name>, Nat, Arc<Expr>)`.
- `Expr::structural_eq(a, b, &mut RecGuard) -> Result<bool, KernelError>` compares **all** fields including binder names, `BinderInfo`, `non_dep`, and `KVMap` (via internal `kvmap_eq`), short-circuiting on `Arc::ptr_eq`. With canonical children it is effectively shallow (one ptr-check per child).
- `ExprNode` variants: `BVar{idx:Nat}`, `FVar{id:Arc<Name>}`, `MVar{id:Arc<Name>}`, `Sort{level:Arc<Level>}`, `Const{name:Arc<Name>, levels:Vec<Arc<Level>>}`, `App{f,arg}`, `Lam{binder_name,binder_type,body,binder_info}`, `ForallE{…same…}`, `LetE{decl_name,ty,value,body,non_dep}`, `Lit(Literal)`, `MData{data:KVMap, expr}`, `Proj{type_name:Arc<Name>, idx:Nat, structure}`.
- `Level` (src/level.rs): variants `Zero`, `Succ(Arc<Level>)`, `Max(Arc<Level>,Arc<Level>)`, `IMax(Arc<Level>,Arc<Level>)`, `Param(Arc<Name>)`, `MVar(Arc<Name>)`. `Level::structural_eq(a,b,&mut RecGuard) -> Result<bool,KernelError>`, `Level::hash_val(&Arc<Level>, &mut RecGuard) -> Result<u64, KernelError>`.
- `RecGuard`: `RecGuard::new()`, `enter(&mut self, f: impl FnOnce(&mut RecGuard) -> Result<R, KernelError>) -> Result<R, KernelError>`.
- `ConstantInfo` variants and their `Arc<Expr>` fields: `Axiom(AxiomVal{val})`, `Defn(DefinitionVal{val,value,..})`, `Thm(TheoremVal{val,value,..})`, `Opaque(OpaqueVal{val,value,..})`, `Quot(QuotVal{val})`, `Induct(InductiveVal{val,..})`, `Ctor(ConstructorVal{val,..})`, `Rec(RecursorVal{val, rules:Vec<RecursorRule{rhs,..}>,..})`. Every `val: ConstantVal` has `ty: Arc<Expr>`. All are `#[derive(Clone)]`.
- CLI `check` (crates/leanr_cli/src/main.rs): builds `constants: HashMap<Arc<Name>, ConstantInfo>`, then (post memfix commit `65096cb`) `drop(loaded);`, then `let mut env = Environment::default(); leanr_kernel::replay(&mut env, constants)`.

## File structure

```
crates/leanr_kernel/src/intern.rs   (new: Interner + intern_level + intern_expr + intern_constant_info + intern_constants + tests)
crates/leanr_kernel/src/lib.rs      (modified: `mod intern;` + `pub use intern::intern_constants;`)
crates/leanr_cli/src/main.rs        (modified: run intern_constants between drop(loaded) and replay)
docs/THREAT_MODEL.md                (modified, Task 4: note the canonicalization pass + its memory characteristic)
```

---

### Task 1: `Interner` scaffold + `Level` interning

**Files:**
- Create: `crates/leanr_kernel/src/intern.rs`
- Modify: `crates/leanr_kernel/src/lib.rs` (add `mod intern;`)
- Test: inline `#[cfg(test)] mod tests` in `intern.rs`

**Interfaces:**
- Produces: `struct Interner` (crate-visible) with `Interner::new()` and `fn intern_level(&mut self, l: &Arc<Level>, g: &mut RecGuard) -> Result<Arc<Level>, KernelError>`. Task 2 adds `intern_expr`, Task 3 adds `intern_constant_info`/`intern_constants`.

- [ ] **Step 1: Write the failing tests**

Add to `crates/leanr_kernel/src/intern.rs` (create the file with just the test module + a stub `Interner` so it compiles-then-fails on behavior; see Step 3 for the real impl — write the test first):

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Level, RecGuard};
    use std::sync::Arc;

    fn name(s: &str) -> Arc<crate::Name> {
        Arc::new(crate::Name::Str {
            parent: Arc::new(crate::Name::Anonymous),
            part: s.to_string(),
        })
    }

    #[test]
    fn level_merges_structurally_equal_distinct_pointers() {
        let mut it = Interner::new();
        let mut g = RecGuard::new();
        // Two independently-built `Succ Zero`s — structurally equal, distinct Arcs.
        let a = Arc::new(Level::Succ(Arc::new(Level::Zero)));
        let b = Arc::new(Level::Succ(Arc::new(Level::Zero)));
        assert!(!Arc::ptr_eq(&a, &b));
        let ca = it.intern_level(&a, &mut g).unwrap();
        let cb = it.intern_level(&b, &mut g).unwrap();
        assert!(Arc::ptr_eq(&ca, &cb), "equal levels must share one canonical Arc");
        assert!(Level::structural_eq(&a, &ca, &mut g).unwrap());
    }

    #[test]
    fn level_distinct_params_not_merged() {
        let mut it = Interner::new();
        let mut g = RecGuard::new();
        let a = Arc::new(Level::Param(name("u")));
        let b = Arc::new(Level::Param(name("v")));
        let ca = it.intern_level(&a, &mut g).unwrap();
        let cb = it.intern_level(&b, &mut g).unwrap();
        assert!(!Arc::ptr_eq(&ca, &cb));
    }

    #[test]
    fn level_idempotent() {
        let mut it = Interner::new();
        let mut g = RecGuard::new();
        let a = Arc::new(Level::Succ(Arc::new(Level::Zero)));
        let ca = it.intern_level(&a, &mut g).unwrap();
        let cca = it.intern_level(&ca, &mut g).unwrap();
        assert!(Arc::ptr_eq(&ca, &cca), "interning a canonical level is a no-op");
    }
}
```

- [ ] **Step 2: Run to verify failure** — `cargo test -p leanr_kernel intern` → compile error (`Interner` undefined) or assertion failure.

- [ ] **Step 3: Implement** the module head + `Interner` + `intern_level`:

```rust
//! Structural interning (hash-consing) for `Expr`/`Level`.
//!
//! A *transient* batch canonicalizer: build an `Interner`, rewrite the
//! decoded constants through it, then drop it. Structurally-identical
//! subterms collapse to one shared `Arc`, so the resulting `Arc` graph
//! (and the `Environment` built from it) holds each distinct subterm once.
//! No global state, no `Weak` refs, no hot-path cost (see
//! docs/superpowers/specs/2026-07-06-expr-hash-consing-design.md).
//!
//! Soundness: interning only ever replaces an `Arc<Expr>`/`Arc<Level>` with
//! a structurally-identical one. The kernel decides types by
//! `structural_eq`/`is_def_eq` (value comparison; `Arc::ptr_eq` is only a
//! fast path), so no verdict can change. Bucket comparison uses the
//! existing `structural_eq`, which compares every field (binder names,
//! `BinderInfo`, `non_dep`, `KVMap`), so merged nodes are fully identical.

use crate::{KernelError, Level, RecGuard};
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Default)]
pub struct Interner {
    /// Canonical levels, bucketed by `Level::hash_val`.
    levels: HashMap<u64, Vec<Arc<Level>>>,
    /// Input-`Arc`-address → canonical level, so a shared input subtree is
    /// interned once. Keys are live for the pass's lifetime only.
    level_memo: HashMap<usize, Arc<Level>>,
    // Expr fields added in Task 2.
}

impl Interner {
    pub fn new() -> Interner {
        Interner::default()
    }

    /// Canonicalize a level bottom-up. Returns the shared canonical `Arc`
    /// for `l`'s structural value.
    pub fn intern_level(
        &mut self,
        l: &Arc<Level>,
        g: &mut RecGuard,
    ) -> Result<Arc<Level>, KernelError> {
        let key = Arc::as_ptr(l) as usize;
        if let Some(c) = self.level_memo.get(&key) {
            return Ok(Arc::clone(c));
        }
        let canon = g.enter(|g| {
            // Rebuild with canonical children first (bottom-up).
            let rebuilt: Arc<Level> = match l.as_ref() {
                Level::Zero | Level::Param(_) | Level::MVar(_) => Arc::clone(l),
                Level::Succ(a) => Arc::new(Level::Succ(self.intern_level(a, g)?)),
                Level::Max(a, b) => {
                    Arc::new(Level::Max(self.intern_level(a, g)?, self.intern_level(b, g)?))
                }
                Level::IMax(a, b) => {
                    Arc::new(Level::IMax(self.intern_level(a, g)?, self.intern_level(b, g)?))
                }
            };
            let h = Level::hash_val(&rebuilt, g)?;
            let bucket = self.levels.entry(h).or_default();
            for existing in bucket.iter() {
                // With canonical children this short-circuits on ptr_eq.
                if Level::structural_eq(existing, &rebuilt, g)? {
                    return Ok(Arc::clone(existing));
                }
            }
            bucket.push(Arc::clone(&rebuilt));
            Ok(rebuilt)
        })?;
        self.level_memo.insert(key, Arc::clone(&canon));
        Ok(canon)
    }
}
```

Add to `crates/leanr_kernel/src/lib.rs` (near the other `mod` lines): `mod intern;` (keep private for now; Task 3 adds the `pub use`).

- [ ] **Step 4: Run tests** — `cargo test -p leanr_kernel intern` → all PASS.
- [ ] **Step 5: Lint and commit**

```bash
mise run lint
git add crates/leanr_kernel/src/intern.rs crates/leanr_kernel/src/lib.rs
git commit -m "feat: Level structural interner (hash-cons scaffold) (hash-consing Task 1)"
```

---

### Task 2: `Expr` interning

**Files:**
- Modify: `crates/leanr_kernel/src/intern.rs`
- Test: inline tests in `intern.rs`

**Interfaces:**
- Consumes: `Interner`, `intern_level` (Task 1).
- Produces: `fn intern_expr(&mut self, e: &Arc<Expr>, g: &mut RecGuard) -> Result<Arc<Expr>, KernelError>`.

- [ ] **Step 1: Write the failing tests** (add to the `tests` module):

```rust
    use crate::Expr;

    fn nat_const(g: &mut RecGuard) -> Arc<Expr> {
        Expr::const_(name("Nat"), vec![], g).unwrap()
    }

    #[test]
    fn expr_merges_structurally_equal_distinct_pointers() {
        let mut it = Interner::new();
        let mut g = RecGuard::new();
        // f x built twice, independently → structurally equal, distinct Arcs.
        let a = Expr::app(nat_const(&mut g), nat_const(&mut g));
        let b = Expr::app(nat_const(&mut g), nat_const(&mut g));
        assert!(!Arc::ptr_eq(&a, &b));
        let ca = it.intern_expr(&a, &mut g).unwrap();
        let cb = it.intern_expr(&b, &mut g).unwrap();
        assert!(Arc::ptr_eq(&ca, &cb), "equal exprs must share one canonical Arc");
    }

    #[test]
    fn expr_shares_common_subterms() {
        let mut it = Interner::new();
        let mut g = RecGuard::new();
        // App(Nat, Nat): after interning, both children are the same Arc.
        let e = Expr::app(nat_const(&mut g), nat_const(&mut g));
        let c = it.intern_expr(&e, &mut g).unwrap();
        let f = Expr::get_app_fn(&c); // the function child
        let args = Expr::get_app_args(&c);
        assert!(Arc::ptr_eq(f, &args[0]), "identical subterms collapse to one Arc");
    }

    #[test]
    fn expr_preserves_structure_and_data() {
        let mut it = Interner::new();
        let mut g = RecGuard::new();
        let e = Expr::app(nat_const(&mut g), nat_const(&mut g));
        let c = it.intern_expr(&e, &mut g).unwrap();
        assert!(Expr::structural_eq(&e, &c, &mut g).unwrap());
        assert_eq!(e.data().hash(), c.data().hash());
    }

    #[test]
    fn expr_idempotent() {
        let mut it = Interner::new();
        let mut g = RecGuard::new();
        let e = Expr::app(nat_const(&mut g), nat_const(&mut g));
        let c = it.intern_expr(&e, &mut g).unwrap();
        let cc = it.intern_expr(&c, &mut g).unwrap();
        assert!(Arc::ptr_eq(&c, &cc));
    }

    #[test]
    fn expr_deep_chain_no_stack_overflow() {
        // A left-nested app chain deep enough to blow a naive stack;
        // RecGuard grows the stack so this returns Ok, and a second
        // identical chain dedups to the same Arc.
        let mut it = Interner::new();
        let mut g = RecGuard::new();
        let build = |g: &mut RecGuard| {
            let mut e = nat_const(g);
            for _ in 0..20_000 {
                e = Expr::app(e, nat_const(g));
            }
            e
        };
        let a = build(&mut g);
        let b = build(&mut g);
        let ca = it.intern_expr(&a, &mut g).unwrap();
        let cb = it.intern_expr(&b, &mut g).unwrap();
        assert!(Arc::ptr_eq(&ca, &cb));
    }
```

- [ ] **Step 2: Run to verify failure** — `cargo test -p leanr_kernel intern` → compile error (`intern_expr` undefined).

- [ ] **Step 3: Implement** — add the expr bucket/memo fields to `Interner` and the method. Update the struct:

```rust
#[derive(Default)]
pub struct Interner {
    levels: HashMap<u64, Vec<Arc<Level>>>,
    level_memo: HashMap<usize, Arc<Level>>,
    /// Canonical exprs, bucketed by `ExprData::hash()` (structural hash).
    exprs: HashMap<u32, Vec<Arc<Expr>>>,
    /// Input-`Arc`-address → canonical expr (per-pass lifetime only).
    expr_memo: HashMap<usize, Arc<Expr>>,
}
```

Add `use crate::{Expr, ExprNode};` to the module imports, then:

```rust
    /// Canonicalize an expr bottom-up. Returns the shared canonical `Arc`
    /// for `e`'s structural value. Guarded recursion (untrusted depth).
    pub fn intern_expr(
        &mut self,
        e: &Arc<Expr>,
        g: &mut RecGuard,
    ) -> Result<Arc<Expr>, KernelError> {
        let key = Arc::as_ptr(e) as usize;
        if let Some(c) = self.expr_memo.get(&key) {
            return Ok(Arc::clone(c));
        }
        let canon = g.enter(|g| {
            // Rebuild with canonical children/levels first (bottom-up).
            // Smart constructors recompute `ExprData`, which is a pure
            // function of children + scalar fields, so the rebuilt node's
            // data equals the original's.
            let rebuilt: Arc<Expr> = match e.node() {
                ExprNode::BVar { .. }
                | ExprNode::FVar { .. }
                | ExprNode::MVar { .. }
                | ExprNode::Lit(_) => Arc::clone(e),
                ExprNode::Sort { level } => Expr::sort(self.intern_level(level, g)?, g)?,
                ExprNode::Const { name, levels } => {
                    let ls = levels
                        .iter()
                        .map(|l| self.intern_level(l, g))
                        .collect::<Result<Vec<_>, _>>()?;
                    Expr::const_(Arc::clone(name), ls, g)?
                }
                ExprNode::App { f, arg } => {
                    Expr::app(self.intern_expr(f, g)?, self.intern_expr(arg, g)?)
                }
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::lam(
                    Arc::clone(binder_name),
                    self.intern_expr(binder_type, g)?,
                    self.intern_expr(body, g)?,
                    *binder_info,
                ),
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::forall_e(
                    Arc::clone(binder_name),
                    self.intern_expr(binder_type, g)?,
                    self.intern_expr(body, g)?,
                    *binder_info,
                ),
                ExprNode::LetE {
                    decl_name,
                    ty,
                    value,
                    body,
                    non_dep,
                } => Expr::let_e(
                    Arc::clone(decl_name),
                    self.intern_expr(ty, g)?,
                    self.intern_expr(value, g)?,
                    self.intern_expr(body, g)?,
                    *non_dep,
                ),
                ExprNode::MData { data, expr } => {
                    Expr::mdata(data.clone(), self.intern_expr(expr, g)?)
                }
                ExprNode::Proj {
                    type_name,
                    idx,
                    structure,
                } => Expr::proj(
                    Arc::clone(type_name),
                    idx.clone(),
                    self.intern_expr(structure, g)?,
                ),
            };
            let h = rebuilt.data().hash();
            let bucket = self.exprs.entry(h).or_default();
            for existing in bucket.iter() {
                // `structural_eq` compares every field and short-circuits on
                // ptr_eq children — effectively shallow here.
                if Expr::structural_eq(existing, &rebuilt, g)? {
                    return Ok(Arc::clone(existing));
                }
            }
            bucket.push(Arc::clone(&rebuilt));
            Ok(rebuilt)
        })?;
        self.expr_memo.insert(key, Arc::clone(&canon));
        Ok(canon)
    }
```

- [ ] **Step 4: Run tests** — `cargo test -p leanr_kernel` → all PASS (Task 1 + Task 2 tests, whole crate).
- [ ] **Step 5: Lint and commit**

```bash
mise run lint
git add crates/leanr_kernel/src/intern.rs
git commit -m "feat: Expr structural interner (bottom-up hash-cons) (hash-consing Task 2)"
```

---

### Task 3: `ConstantInfo` + constants-map canonicalization

**Files:**
- Modify: `crates/leanr_kernel/src/intern.rs`, `crates/leanr_kernel/src/lib.rs`
- Test: inline tests in `intern.rs`

**Interfaces:**
- Consumes: `Interner`, `intern_expr` (Task 2), `ConstantInfo` (already exported).
- Produces (crate public API): `pub fn intern_constants(constants: HashMap<Arc<Name>, ConstantInfo>) -> Result<HashMap<Arc<Name>, ConstantInfo>, KernelError>`. Re-exported from `lib.rs` as `leanr_kernel::intern_constants`.

- [ ] **Step 1: Write the failing tests** (add to `tests`):

```rust
    use crate::{ConstantInfo, Name};

    // Build two axioms in two "modules" whose types are the SAME structure
    // (App(Nat, Nat)) but distinct Arcs, then intern the whole map and
    // assert the two types now share one canonical Arc.
    #[test]
    fn constants_map_shares_across_entries() {
        let mut g = RecGuard::new();
        let mk_axiom = |g: &mut RecGuard| {
            let ty = Expr::app(nat_const(g), nat_const(g));
            ConstantInfo::Axiom(crate::AxiomVal {
                val: crate::ConstantVal {
                    name: name("A"),
                    level_params: vec![],
                    ty,
                },
                is_unsafe: false,
            })
        };
        let mut map: HashMap<Arc<Name>, ConstantInfo> = HashMap::new();
        map.insert(name("A"), mk_axiom(&mut g));
        map.insert(name("B"), mk_axiom(&mut g));
        let out = intern_constants(map).unwrap();
        let ta = &out[&name("A")].constant_val().ty;
        let tb = &out[&name("B")].constant_val().ty;
        assert!(Arc::ptr_eq(ta, tb), "identical types across entries collapse to one Arc");
    }

    #[test]
    fn constants_map_preserves_each_type() {
        let mut g = RecGuard::new();
        let ty = Expr::app(nat_const(&mut g), nat_const(&mut g));
        let orig = ty.clone();
        let ci = ConstantInfo::Axiom(crate::AxiomVal {
            val: crate::ConstantVal { name: name("A"), level_params: vec![], ty },
            is_unsafe: false,
        });
        let mut map = HashMap::new();
        map.insert(name("A"), ci);
        let out = intern_constants(map).unwrap();
        assert!(Expr::structural_eq(&orig, &out[&name("A")].constant_val().ty, &mut g).unwrap());
    }
```

> NOTE to implementer: `AxiomVal`, `ConstantVal`, `ConstantInfo`, `Name` are already `pub use`d from `lib.rs` (verified). `AxiomVal` fields: `val: ConstantVal`, `is_unsafe: bool`. `ConstantVal` fields: `name: Arc<Name>`, `level_params: Vec<Arc<Name>>`, `ty: Arc<Expr>`. The fixtures above compile as written — no visibility changes needed.

- [ ] **Step 2: Run to verify failure** — `cargo test -p leanr_kernel intern` → compile error (`intern_constants` undefined).

- [ ] **Step 3: Implement** — add `intern_constant_info` (private method) and the free function `intern_constants`. Add `use crate::{ConstantInfo, Name};` and a `HashMap` import as needed.

```rust
impl Interner {
    /// Canonicalize every `Arc<Expr>` reachable from a `ConstantInfo`.
    fn intern_constant_info(
        &mut self,
        ci: &ConstantInfo,
        g: &mut RecGuard,
    ) -> Result<ConstantInfo, KernelError> {
        let mut out = ci.clone();
        match &mut out {
            ConstantInfo::Axiom(v) => {
                let t = self.intern_expr(&v.val.ty, g)?;
                v.val.ty = t;
            }
            ConstantInfo::Defn(v) => {
                let t = self.intern_expr(&v.val.ty, g)?;
                v.val.ty = t;
                let val = self.intern_expr(&v.value, g)?;
                v.value = val;
            }
            ConstantInfo::Thm(v) => {
                let t = self.intern_expr(&v.val.ty, g)?;
                v.val.ty = t;
                let val = self.intern_expr(&v.value, g)?;
                v.value = val;
            }
            ConstantInfo::Opaque(v) => {
                let t = self.intern_expr(&v.val.ty, g)?;
                v.val.ty = t;
                let val = self.intern_expr(&v.value, g)?;
                v.value = val;
            }
            ConstantInfo::Quot(v) => {
                let t = self.intern_expr(&v.val.ty, g)?;
                v.val.ty = t;
            }
            ConstantInfo::Induct(v) => {
                let t = self.intern_expr(&v.val.ty, g)?;
                v.val.ty = t;
            }
            ConstantInfo::Ctor(v) => {
                let t = self.intern_expr(&v.val.ty, g)?;
                v.val.ty = t;
            }
            ConstantInfo::Rec(v) => {
                let t = self.intern_expr(&v.val.ty, g)?;
                v.val.ty = t;
                for rule in &mut v.rules {
                    let rhs = self.intern_expr(&rule.rhs, g)?;
                    rule.rhs = rhs;
                }
            }
        }
        Ok(out)
    }
}

/// Batch-canonicalize a decoded constants map. Structurally-identical
/// subterms across all entries collapse to one shared `Arc`; the returned
/// map's `Arc` graph carries that sharing (the `Interner` itself is dropped
/// here). Verdict-preserving (see module docs). Errors only on
/// `KernelError::DeepRecursion` for adversarially deep input.
pub fn intern_constants(
    constants: HashMap<Arc<Name>, ConstantInfo>,
) -> Result<HashMap<Arc<Name>, ConstantInfo>, KernelError> {
    let mut it = Interner::new();
    let mut g = RecGuard::new();
    let mut out = HashMap::with_capacity(constants.len());
    for (name, ci) in constants {
        let interned = it.intern_constant_info(&ci, &mut g)?;
        drop(ci); // release the original entry as we go
        out.insert(name, interned);
    }
    Ok(out)
}
```

Add to `lib.rs`: change `mod intern;` to keep the module private but re-export the function — add `pub use intern::intern_constants;` beside the other `pub use` lines.

- [ ] **Step 4: Run tests** — `cargo test -p leanr_kernel` → all PASS.
- [ ] **Step 5: Lint and commit**

```bash
mise run lint
git add crates/leanr_kernel/src/intern.rs crates/leanr_kernel/src/lib.rs
git commit -m "feat: batch-canonicalize decoded constants map (hash-consing Task 3)"
```

---

### Task 4: Wire into `leanr check` + verdict-preservation gate + docs

**Files:**
- Modify: `crates/leanr_cli/src/main.rs` (the `check` fn), `docs/THREAT_MODEL.md`
- Test: `crates/leanr_olean/tests/check_fixtures.rs` is the verdict gate (already exists — must stay green); no new test file.

**Interfaces:**
- Consumes: `leanr_kernel::intern_constants` (Task 3).

- [ ] **Step 1: Add the interning call.** In `crates/leanr_cli/src/main.rs`, in `check`, between the existing `drop(loaded);` and the `let mut env = Environment::default();`, insert:

```rust
    // Structurally intern the decoded constants before replay: collapse
    // duplicate subterms (Nat, Prop, common signatures) shared across the
    // whole module set into one Arc each, cutting the Environment's peak
    // memory. Verdict-preserving (leanr_kernel::intern; hash-consing spec).
    let constants = match leanr_kernel::intern_constants(constants) {
        Ok(c) => c,
        Err(err) => {
            eprintln!("error: interning decoded constants failed: {err}");
            return ExitCode::FAILURE;
        }
    };
```

(If `drop(loaded);` is absent for any reason, add it immediately before this block — `loaded` must not be held during interning or replay.)

- [ ] **Step 2: Verify the fixture/mutation suite still passes (the verdict gate).**

Run: `cargo test --workspace`
Expected: all PASS — in particular `check_fixtures.rs` (real replay of `Prelude0`/hermetic fixtures + `mutation_verdicts_match` hermetic mutation-differential). Zero verdict drift. If anything fails, STOP: interning changed a verdict — that is a defect in Tasks 1-3, debug via systematic-debugging (do not adjust the test).

- [ ] **Step 3: Quick CLI smoke on a hermetic fixture** — confirm `check` still succeeds end-to-end with interning wired in:

Run: `cargo run --release -p leanr_cli -- check --help`
Expected: usage prints, exit 0. (The full stdlib acceptance sweep is the controller's Step 5, not run here.)

- [ ] **Step 4: Document** — in `docs/THREAT_MODEL.md`, add a short note under the memory/DoS discussion: the checker structurally interns decoded constants before replay (a bounded, single batch pass, `RecGuard`-guarded like all term recursion); this reduces the resident footprint of the whole-environment check and is verdict-preserving (only structurally-identical subterms are shared). Keep it to 2-4 sentences, matching the file's existing tone.

- [ ] **Step 5: Lint and commit**

```bash
mise run lint
git add crates/leanr_cli/src/main.rs docs/THREAT_MODEL.md
git commit -m "perf: intern decoded constants in leanr check before replay (hash-consing Task 4)"
```

- [ ] **Step 6: ACCEPTANCE (controller-run, not a subagent step).** The controller re-runs the full stdlib sweep under the memory watchdog:
  `cargo run --release -p leanr_cli -- check --all --path "$(lean --print-libdir)"`
  - **Pass:** exit 0 with `checked 2433 modules, <M> declarations …`, peak comfortably under 32 GiB. Record peak + wall-clock + declaration count.
  - If the peak is NOT comfortably under 32 GiB (target: meaningful headroom, e.g. ≤ ~24 GiB), proceed to Task 5. Otherwise Task 5 is skipped (YAGNI) and this plan is complete.

---

### Task 5 (GATED — do only if Task 4 Step 6's measured peak lacks comfortable headroom under 32 GiB)

**Rationale:** Task 4 interns *decoded* constants. Kernel-*generated* recursors (from inductive admission) are built fresh during replay and are not interned, so their internal subterms don't share with the canonicalized pool. If the decoded-constant pass alone does not free enough, extend interning to those.

**Files:**
- Modify: `crates/leanr_kernel/src/intern.rs` (expose a persistent per-replay interner or a `intern_expr` entry usable mid-replay), `crates/leanr_kernel/src/env.rs` and/or `crates/leanr_kernel/src/inductive.rs` (intern generated `ConstantInfo` exprs as they are inserted into the `Environment`), `crates/leanr_kernel/src/replay.rs` (thread the interner through admission).

- [ ] **Step 1:** Design the threading first (write it into this task before coding): the `replay` driver owns one `Interner` for the whole run; `add_decl`/inductive admission interns each generated expr before storing it in `env`. Keep it an explicit value (no global state), guarded recursion throughout. Re-confirm verdict preservation (`cargo test --workspace` green) since this now touches the trusted admission path.
- [ ] **Step 2-5:** TDD each interning site (unit test: a generated recursor's shared subterms collapse), implement, `cargo test --workspace` green, `mise run lint`, commit `perf: intern kernel-generated exprs during replay (hash-consing Task 5)`.
- [ ] **Step 6:** Controller re-runs the acceptance sweep; confirm comfortable headroom.

---

## Plan self-review (performed at write time)

1. **Spec coverage:** batch canonicalization before replay (T3/T4), transient strong-ref interner dropped after the pass (T3 `intern_constants`), bottom-up shallow-effective bucket key via `ExprData::hash()` + `structural_eq` (T2), level interning included in the core (T1), guarded recursion via `RecGuard` (T1/T2), soundness/verdict-preservation gate (T4 Step 2), acceptance sweep under watchdog (T4 Step 6), gated recursor interning (T5). THREAT_MODEL note (T4 Step 4). ✓
2. **Placeholder scan:** every code step carries complete code; test bodies are concrete; the one NOTE (T3 Step 1) is a visibility confirmation with an explicit fallback, not a deferred design. ✓
3. **Type consistency:** `Interner`/`intern_level` (T1) → `intern_expr` (T2) → `intern_constant_info`/`intern_constants` (T3) → CLI call (T4). Signatures match `RecGuard::enter`, the smart-constructor return types (`sort`/`const_` are `Result`, others infallible), and `ConstantInfo` field names verified against decl.rs. ✓
4. **YAGNI:** Task 5 is explicitly gated on measurement; the core (T1-T4) is the minimal path to the memory win. ✓
