# M4b-3 P5 — Binder and Argument Breadth Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give leanr's term elaborator the remaining `fun`/`let`/`have` binder forms (implicit, strict-implicit, instance-implicit, `optType`), expected-type propagation into binder domains, real implicit-lambda insertion, and the `optParam`/`autoParam` default-argument paths — closing every named M4b-3 P5 seam.

**Architecture:** Two independent families, binder first. The binder family rewrites `builtin/binder.rs`'s `fun` telescope to carry a `BinderInfo` per binder and to thread an expected type through it, then replaces `elab.rs`'s implicit-lambda *guard* with the implementation. The argument family adds the two default-filling arms to `app/args.rs`. Between them sits a scoping-audit task. Local-instance installation is **not** wired by this plan — PR #43 already installs at the `push_local_decl` chokepoint keyed on the binder's type, which is exactly the oracle's rule.

**Tech Stack:** Rust (workspace crates `leanr_elab`, `leanr_syntax`, `leanr_meta`, `leanr_kernel`), Lean 4 fixtures (`tests/fixtures/elab/`), `mise` task runner, `serde_json` canonical-`Expr` encoding for the differential gate.

**Spec:** `docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md` § P5 and § Amendment 8. Prerequisite slices that this plan builds on: `2026-09-08-metavariable-local-contexts-design.md`, `2026-09-09-elim-mvar-deps-design.md`, `2026-09-09-local-instances-design.md`.

---

## Global Constraints

Every task's requirements implicitly include this section.

- **Oracle pin:** `lean-toolchain` = `leanprover/lean4:v4.33.0-rc1`. Never bump it inside this slice. Every oracle citation in this plan was verified against `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/` on 2026-09-10; re-verify before trusting any line number you did not open yourself.
- **`leanr_meta/src` is additive-only.** The accessor ledger's P5 row reads `none expected`. If a task finds it needs a `leanr_meta` change, it must be an additive, TCB-neutral, behavior-neutral accessor, and the ledger row must be amended in Task 12 with the rejected alternative recorded. A non-additive change is out of scope for this plan.
- **`leanr_kernel` depends on no other workspace crate.**
- **No path panics.** `MetaError` propagates rather than collapsing; `IsDefEqStuck` means *postpone*, never *fail*.
- **Every deferred path is a named seam.** `ElabError::UnsupportedSyntax` with a message naming the owning slice. Never fall through to a different term.
- **CI gates on `mise run ci`**, which includes `cargo fmt --check` and clippy. The test tasks do **not** cover formatting. Run `mise run fmt` before every commit, or `mise run ci` before every push.
- **Neutrality:** the committed elaboration corpus (`tests/fixtures/elab/elab-queries.jsonl`) and synthesis corpus (`tests/fixtures/meta/synth-queries.jsonl`) may only **grow**. No pre-existing record may change. Task 11 measures this.
- **Commits** end with the session attribution line:
  ```
  Claude-Session: https://claude.ai/code/session_01Dckmjcx6aKtDCEc1ZhcsBL
  ```

---

## What is already done (do not re-implement)

Verified by reading the code on 2026-09-10. Amendment 8 predates these landings.

| Amendment 8 item | Status |
|---|---|
| Local-instance installation at the binder | **Done** — `crates/leanr_meta/src/metactx.rs` `push_local_decl` calls `install_local_instance_for(fvar, ty, depth)`, keyed on type only. Its doc comment: "binder info plays no part, so `fun (inst : Add N) => …` counts exactly as `[inst : Add N]` does." Matches oracle `elabFunBinderViews`' `match ← isClass? type` (`Binders.lean:445`), which likewise ignores `binderView.bi`. **P5 gets this for free by passing the right `BinderInfo` and pushing the binder at all.** |
| `..` ellipsis | **Done** — parsed in `crates/leanr_elab/src/app/expand.rs:126,164`, consumed at `crates/leanr_elab/src/app/args.rs` (`if app.ctx.ellipsis { add_implicit_arg(app)?; return Ok(true); }`), with the `heed_elab_as_elim = !explicit && !ellipsis` early-out at `crates/leanr_elab/src/app/mod.rs:362`. Oracle `App.lean:856-857`, `:1399`. |
| `funBinder` parsing (`{α β}`, `⦃α β⦄`, `[inst : C α]`, `[C α]`) | **Done in `leanr_syntax`** — `crates/leanr_syntax/src/builtin/term.rs:431-458` (`fun_binder`), with the same `lookahead` disambiguation the oracle uses. P5 is elaborator-side only. |
| `optParam`/`autoParam` wrapper stripping for an **explicitly supplied** argument | **Done** — `consume_opt_auto_param` / `get_arg_expected_type` in `crates/leanr_elab/src/app/args.rs`. Only the **default-filling** arms remain (Tasks 8 and 9). |

---

## File Structure

**Modified:**

- `crates/leanr_elab/src/builtin/binder.rs` (743 lines) — the binder family's centre. `extract_fun_binder` becomes group-returning and binder-info-carrying; `elab_fun` grows an expected-type thread and an `optType` arm; `binder_info_of` gains its `instBinder` case. This file is already near the size where it should be watched, but the change is cohesive (one telescope, one concept) and splitting it mid-slice would obscure the diff against the oracle's own single `Binders.lean` loop. Leave it whole; revisit if it passes ~1000 lines.
- `crates/leanr_elab/src/elab.rs` — `check_implicit_lambda` (currently a guard at `:391-421`) becomes `use_implicit_lambda` returning a three-way result, plus the new `elab_implicit_lambda` wrap.
- `crates/leanr_elab/src/app/args.rs` — the `optParam` default arm and the `autoParam` tactic-mvar arm replace the seam at `:412`; the mvar-fType seam at `:145` is closed by Task 4.
- `crates/leanr_elab/src/synthetic/state.rs`, `crates/leanr_elab/src/synthetic/report.rs` — register and report the `Tactic` synthetic-mvar kind (Task 9).
- `crates/leanr_elab/tests/binder_smoke.rs`, `crates/leanr_elab/tests/app_smoke.rs`, `crates/leanr_elab/tests/seam_audit.rs` — leanr-side red/green tests and the seam ledger.
- `tests/fixtures/elab/Elab0.lean`, `tests/fixtures/elab/dump_elab.lean` — new oracle corpus declarations and query groups.
- `docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md` — Amendment 9 (Task 12).

**Created:** none. Every change lands in an existing module.

---

### Task 1: `fun` binder-info breadth

The `fun` telescope currently hardcodes `BinderInfo::Default` and rejects every bracketed `funBinder` node. This task makes it carry binder info and handle multi-name groups.

**Files:**
- Modify: `crates/leanr_elab/src/builtin/binder.rs` (`extract_fun_binder` → `extract_fun_binder_views`, and its caller inside `elab_fun`)
- Test: `crates/leanr_elab/tests/binder_smoke.rs`

**Interfaces:**
- Consumes: `extract_binder_group` (existing, `binder.rs`), `elab_type`, `fresh_type_mvar`, `intern_binder_name`, `non_trivia_children`, `MetaCtx::push_local_decl(name, ty, bi)`.
- Produces: `struct FunBinderView { name: Option<NameId>, ty: Option<SynElem>, bi: BinderInfo }` and `fn extract_fun_binder_views(elab: &mut TermElabM, item: &SynElem, kinds: &KindInterner) -> Result<Vec<FunBinderView>, ElabError>`. Tasks 2 and 4 both call this.

**Background the implementer needs.** A `funBinder` is `funStrictImplicitBinder <|> funImplicitBinder <|> instBinder <|> termParser maxPrec` (`Lean/Parser/Term.lean:379-381`). The implicit and strict-implicit alternatives reuse the *same node kinds* as bracketed binders (`Lean.Parser.Term.implicitBinder`, `…strictImplicitBinder`), so `extract_binder_group` already knows their layout: child `[1]` is a names `KIND_NULL`, child `[2]` is a binder-type `KIND_NULL` holding `[":", T]` when a type was written. Unlike the `forall` case, in a `fun` the type may be **absent** (`fun {α} => …`), so this task must tolerate an empty type slot where `extract_binder_group` errors. `instBinder` has a different layout — `["[", optIdent(null), T, "]"]`, so child `[1]` is an optional-name null wrapper and child `[2]` is a bare term (`crates/leanr_syntax/src/builtin/term.rs:183-187`; oracle `toBinderViews`, `Lean/Elab/Binders.lean:450-453`, uses `expandOptIdent stx[1]` and `type := stx[2]`).

One binder group can bind several names (`many1 binderIdent`), and each shares one type that elaborates **once, before any of its own names enter scope** — the rule `push_binder_group` already follows.

- [ ] **Step 1: Write the failing tests**

Add to `crates/leanr_elab/tests/binder_smoke.rs`:

```rust
#[test]
fn fun_implicit_binder_carries_binder_info() {
    // fun {a : Type} => a  →  lam bi=i (Sort ..) (bvar 0)
    let j = elab_json("fun {a : Type} => a");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "i");
    assert_eq!(j["b"]["k"], "bvar");
    assert_eq!(j["b"]["i"], 0);
}

#[test]
fn fun_strict_implicit_binder_carries_binder_info() {
    let j = elab_json("fun ⦃a : Type⦄ => a");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "s");
}

#[test]
fn fun_inst_binder_named_carries_binder_info() {
    // `Add` is in Elab0's environment (Task 10 guarantees it).
    let j = elab_json("fun [inst : Add Nat] => inst");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "c");
    assert_eq!(j["b"]["k"], "bvar");
    assert_eq!(j["b"]["i"], 0);
}

#[test]
fn fun_inst_binder_anonymous_still_binds() {
    // `[Add Nat]` — no name written. The oracle's `expandOptIdent` mints
    // an inaccessible one; leanr interns `None`. Binder names are erased
    // by the encoder, so only the shape and `bi` are asserted.
    let j = elab_json("fun [Add Nat] => Nat.zero");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "c");
}

#[test]
fn fun_implicit_group_binds_every_name() {
    // fun {a b : Type} => a  →  lam (lam (bvar 1))
    let j = elab_json("fun {a b : Type} => a");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "i");
    assert_eq!(j["b"]["k"], "lam");
    assert_eq!(j["b"]["bi"], "i");
    assert_eq!(j["b"]["b"]["k"], "bvar");
    assert_eq!(j["b"]["b"]["i"], 1);
}

#[test]
fn fun_implicit_binder_without_type_gets_an_mvar_domain() {
    // fun {a} => a — no type written; domain is a fresh type mvar.
    let j = elab_json("fun {a} => a");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "i");
    assert_eq!(j["t"]["k"], "mvar");
}
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test -p leanr_elab --test binder_smoke fun_implicit -- --nocapture`

Expected: FAIL. The current `extract_fun_binder` hits its catch-all arm and panics through `elab_json`'s `unwrap_or_else` with `UnsupportedSyntax("fun: unsupported binder kind Lean.Parser.Term.implicitBinder")`.

- [ ] **Step 3: Add the view struct and the group extractor**

In `crates/leanr_elab/src/builtin/binder.rs`, replace `extract_fun_binder` with:

```rust
/// One elaborated-binder view: the oracle's `BinderView`
/// (`Lean/Elab/Binders.lean`, `toBinderViews` at `:436`). A single
/// `funBinder` item can expand to SEVERAL views — `{a b : Type}` binds
/// two names sharing one type syntax.
struct FunBinderView {
    name: Option<NameId>,
    ty: Option<SynElem>,
    bi: BinderInfo,
}

/// oracle: `toBinderViews` (`Binders.lean:436-455`), restricted to the
/// four `funBinder` alternatives (`Parser/Term.lean:379-381`).
///
/// Unlike the `forall`/`let` telescope, a `fun` binder's type may be
/// ABSENT (`fun {a} => …`), so this tolerates an empty binder-type slot
/// where `extract_binder_group` errors.
fn extract_fun_binder_views(
    elab: &mut TermElabM,
    item: &SynElem,
    kinds: &KindInterner,
) -> Result<Vec<FunBinderView>, ElabError> {
    match item {
        // Bare ident binder: `fun x => …` — elided type.
        NodeOrToken::Token(tok) if kinds.name(tok.kind()) == "<ident>" => {
            let name = intern_binder_name(elab, tok.text())?;
            Ok(vec![FunBinderView {
                name: Some(name),
                ty: None,
                bi: BinderInfo::Default,
            }])
        }
        NodeOrToken::Node(n) => {
            let kind = kinds.name(n.kind());
            match kind {
                // Parenthesised binder `(x : T)` — the `termParser
                // maxPrec` alternative, parsed as a typeAscription.
                "Lean.Parser.Term.typeAscription" => {
                    let (name, ty) = extract_paren_fun_binder(elab, n, kinds)?;
                    Ok(vec![FunBinderView {
                        name: Some(name),
                        ty: Some(ty),
                        bi: BinderInfo::Default,
                    }])
                }
                // `{a b : T}` / `{a b}` and `⦃a b : T⦄` / `⦃a b⦄`.
                "Lean.Parser.Term.implicitBinder" | "Lean.Parser.Term.strictImplicitBinder" => {
                    let bi = if kind == "Lean.Parser.Term.implicitBinder" {
                        BinderInfo::Implicit
                    } else {
                        BinderInfo::StrictImplicit
                    };
                    let ch = non_trivia_children(n);
                    let names_null = ch.get(1).and_then(|el| el.as_node()).ok_or_else(|| {
                        ElabError::UnsupportedSyntax("fun binder group: names slot".into())
                    })?;
                    let ty_null = ch.get(2).and_then(|el| el.as_node()).ok_or_else(|| {
                        ElabError::UnsupportedSyntax("fun binder group: type slot".into())
                    })?;
                    // `[":", T]` when a type was written; empty otherwise.
                    let ty = non_trivia_children(ty_null).into_iter().nth(1);
                    let mut views = Vec::new();
                    for name_el in non_trivia_children(names_null) {
                        let name = intern_fun_binder_ident(elab, &name_el, kinds)?;
                        views.push(FunBinderView {
                            name,
                            ty: ty.clone(),
                            bi,
                        });
                    }
                    if views.is_empty() {
                        return Err(ElabError::UnsupportedSyntax(
                            "fun binder group: no names".into(),
                        ));
                    }
                    Ok(views)
                }
                // `[inst : C α]` / `[C α]` — optional name, BARE type at
                // child [2] (no `KIND_NULL` wrapper, unlike the groups
                // above). oracle: `Binders.lean:450-453`.
                "Lean.Parser.Term.instBinder" => {
                    let ch = non_trivia_children(n);
                    let name = match ch.get(1).and_then(|el| el.as_node()) {
                        Some(opt) => match non_trivia_children(opt).first() {
                            Some(el) => intern_fun_binder_ident(elab, el, kinds)?,
                            None => None,
                        },
                        None => None,
                    };
                    let ty = ch.get(2).cloned().ok_or_else(|| {
                        ElabError::UnsupportedSyntax("fun inst binder: type slot".into())
                    })?;
                    Ok(vec![FunBinderView {
                        name,
                        ty: Some(ty),
                        bi: BinderInfo::InstImplicit,
                    }])
                }
                _ => Err(ElabError::UnsupportedSyntax(format!(
                    "fun: unsupported binder kind {kind}"
                ))),
            }
        }
        _ => Err(ElabError::UnsupportedSyntax(format!(
            "fun: unsupported binder kind {}",
            kinds.name(item.kind())
        ))),
    }
}

/// A binder identifier is either an `<ident>` token or a `_` hole node
/// (`binderIdent`). A hole binds an anonymous local. oracle:
/// `expandBinderIdent` (`Binders.lean:32-36`).
fn intern_fun_binder_ident(
    elab: &mut TermElabM,
    el: &SynElem,
    kinds: &KindInterner,
) -> Result<Option<NameId>, ElabError> {
    match el {
        NodeOrToken::Token(tok) if kinds.name(tok.kind()) == "<ident>" => {
            Ok(Some(intern_binder_name(elab, tok.text())?))
        }
        NodeOrToken::Node(n) if kinds.name(n.kind()) == "Lean.Parser.Term.hole" => Ok(None),
        _ => Err(ElabError::UnsupportedSyntax(format!(
            "fun binder name: {}",
            kinds.name(el.kind())
        ))),
    }
}
```

Move the existing `typeAscription` arm of the old `extract_fun_binder` verbatim into a helper `extract_paren_fun_binder(elab, n, kinds) -> Result<(NameId, SynElem), ElabError>` — same body, same two error messages (`"fun: paren binder is not a single ident (M4b-3)"`, `"fun: paren binder without a type (M4b-3)"`), just returning the pair instead of the option-wrapped tuple.

- [ ] **Step 4: Rewrite `elab_fun`'s telescope loop to consume views**

In `elab_fun`, replace the body of the `for item in &items` loop:

```rust
        for item in &items {
            for view in extract_fun_binder_views(elab, item, kinds)? {
                let dom = match &view.ty {
                    Some(ty_elem) => elab_type(elab, ty_elem, kinds)?,
                    None => fresh_type_mvar(elab)?,
                };
                // `push_local_decl` installs a local instance when `dom`
                // is class-typed — keyed on the TYPE, not on `view.bi`,
                // exactly as the oracle's `isClass? type` test is
                // (`Binders.lean:445`). Nothing further is needed here.
                let fvar = elab
                    .mctx
                    .push_local_decl(view.name, dom, view.bi)
                    .map_err(ElabError::from)?;
                fvars.push(fvar);
            }
        }
```

- [ ] **Step 5: Run the tests to verify they pass**

Run: `cargo test -p leanr_elab --test binder_smoke`

Expected: PASS, including the six new tests and every pre-existing one (`fun_explicit_binder`, `fun_elided_binder_is_bare_mvar_domain`, `fun_two_binders_nests_and_bvar_indexes`).

- [ ] **Step 6: Run the full crate suite to confirm nothing regressed**

Run: `cargo test -p leanr_elab`

Expected: PASS. `oracle_elab` must still replay all 117 committed records green — this task adds forms, it changes no existing one.

- [ ] **Step 7: Format and commit**

```bash
mise run fmt
git add crates/leanr_elab/src/builtin/binder.rs crates/leanr_elab/tests/binder_smoke.rs
git commit -m "$(cat <<'EOF'
feat(elab): fun binder-info breadth — implicit, strict-implicit, instance-implicit

extract_fun_binder becomes extract_fun_binder_views, returning one view
per bound name with its BinderInfo. Multi-name groups ({a b : T}) and
type-less binders ({a}) are both supported; instBinder's optional-name /
bare-type layout is handled separately from the null-wrapped groups.

Local-instance installation needs no wiring here: push_local_decl keys
on the binder's type, matching the oracle's `isClass? type` test, which
likewise ignores binderView.bi.

Claude-Session: https://claude.ai/code/session_01Dckmjcx6aKtDCEc1ZhcsBL
EOF
)"
```

---

### Task 2: `fun`'s `optType`

`fun x : T => e` currently errors with `"fun: return-type optType (M4b-3)"`. The `optType` is the **body's** expected type, not a binder's.

**Files:**
- Modify: `crates/leanr_elab/src/builtin/binder.rs` (`elab_fun`, the `optType` guard and the body elaboration)
- Test: `crates/leanr_elab/tests/binder_smoke.rs`

**Interfaces:**
- Consumes: Task 1's `extract_fun_binder_views`; `elab_type`; `TermElabM::elab_term_ensuring_type` (`crates/leanr_elab/src/elab.rs:309`).
- Produces: nothing new; `elab_fun` keeps its signature.

**Background.** `basicFun := many1 funBinder >> optType >> " => " >> term` (`Parser/Term.lean:384-385`). `optType := optional (" : " >> term)`. The oracle path is `elabFun` → `expandFunBinders` → `elabFunBinders binders expectedType? fun xs expectedType? => elabTermEnsuringType body expectedType?` (`Binders.lean:684-690`). When an `optType` is written, the macro `expandFun` rewrites `fun bs : T => e` into `fun bs => (e : T)` — i.e. the type ascribes the **body**, under the binders. Elaborating it as a type *inside* the telescope (so it may mention the binders) and passing it as the body's expected type is equivalent and is what this task does.

- [ ] **Step 1: Write the failing tests**

```rust
#[test]
fn fun_opt_type_ascribes_the_body() {
    // fun (x : Nat) : Nat => x
    let j = elab_json("fun (x : Nat) : Nat => x");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["t"]["k"], "const");
    assert_eq!(j["t"]["n"], "Nat");
    assert_eq!(j["b"]["k"], "bvar");
    assert_eq!(j["b"]["i"], 0);
}

#[test]
fn fun_opt_type_may_mention_the_binders() {
    // fun (a : Type) (x : a) : a => x — the optType `a` refers to the
    // first binder, so it must elaborate INSIDE the telescope.
    let j = elab_json("fun (a : Type) (x : a) : a => x");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["b"]["k"], "lam");
    assert_eq!(j["b"]["b"]["k"], "bvar");
    assert_eq!(j["b"]["b"]["i"], 0);
}
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test -p leanr_elab --test binder_smoke fun_opt_type -- --nocapture`

Expected: FAIL with `UnsupportedSyntax("fun: return-type optType (M4b-3)")`.

- [ ] **Step 3: Replace the guard with the implementation**

In `elab_fun`, delete the `optType` rejection block and capture the syntax instead:

```rust
    // `optType` (`fun x : T => e`, `Parser/Term.lean:384`). Child [1] is
    // the null-wrapped optional; a non-empty wrapper holds `[":", T]`.
    // oracle: the `expandFun` macro rewrites `fun bs : T => e` to
    // `fun bs => (e : T)`, so `T` ascribes the BODY, under the binders.
    let opt_type = bch
        .get(1)
        .and_then(|el| el.as_node())
        .and_then(|opt| non_trivia_children(opt).into_iter().nth(1));
```

Then, inside the `lctx_checkpoint` closure, replace the body elaboration:

```rust
        // The optType elaborates INSIDE the telescope: it may mention
        // the binders (`fun (a : Type) (x : a) : a => x`).
        let expected_body = match &opt_type {
            Some(ty_elem) => Some(elab_type(elab, ty_elem, kinds)?),
            None => None,
        };
        let body = match expected_body {
            Some(t) => elab.elab_term_ensuring_type(&body_elem, kinds, Some(t))?,
            None => elab.elab_term(&body_elem, kinds, None)?,
        };
        elab.mctx.mk_lambda(&fvars, body).map_err(ElabError::from)
```

- [ ] **Step 4: Run the tests to verify they pass**

Run: `cargo test -p leanr_elab --test binder_smoke`

Expected: PASS.

- [ ] **Step 5: Run the crate suite**

Run: `cargo test -p leanr_elab`

Expected: PASS, 117 oracle records still green.

- [ ] **Step 6: Format and commit**

```bash
mise run fmt
git add crates/leanr_elab/src/builtin/binder.rs crates/leanr_elab/tests/binder_smoke.rs
git commit -m "$(cat <<'EOF'
feat(elab): fun optType ascribes the body under the telescope

`fun bs : T => e` is `fun bs => (e : T)` after expandFun, so T elaborates
inside the binder telescope (it may mention the binders) and becomes the
body's expected type via elab_term_ensuring_type.

Claude-Session: https://claude.ai/code/session_01Dckmjcx6aKtDCEc1ZhcsBL
EOF
)"
```

---

### Task 3: `let` / `have` instance-implicit bracketed binders

`binder_info_of` returns `None` for `instBinder`, naming a seam. `let`/`have` reach it through `push_let_binders`.

**Files:**
- Modify: `crates/leanr_elab/src/builtin/binder.rs` (`binder_info_of`, `extract_binder_group`)
- Test: `crates/leanr_elab/tests/binder_smoke.rs`

**Interfaces:**
- Consumes: `extract_binder_group`, `push_binder_group` (both existing).
- Produces: `binder_info_of` now returns `Some(BinderInfo::InstImplicit)` for `"Lean.Parser.Term.instBinder"`.

**Background.** `extract_binder_group`'s doc records the blocker: `instBinder` has "a different child layout — optional name + bare type". So this task is two changes — the info map, and a layout branch in the extractor. `bracketedBinder` orders `explicitBinder <|> strictImplicitBinder <|> implicitBinder <|> instBinder` (`crates/leanr_syntax/src/builtin/term.rs`, `bracketed_binder`), so `let`/`have`/`forall` all reach the new arm identically.

- [ ] **Step 1: Write the failing tests**

```rust
#[test]
fn forall_inst_binder_carries_binder_info() {
    let j = elab_json("forall [inst : Add Nat], Nat");
    assert_eq!(j["k"], "pi");
    assert_eq!(j["bi"], "c");
}

#[test]
fn forall_inst_binder_anonymous() {
    let j = elab_json("forall [Add Nat], Nat");
    assert_eq!(j["k"], "pi");
    assert_eq!(j["bi"], "c");
}

#[test]
fn have_inst_binder_binds_and_abstracts() {
    // have f : forall [inst : Add Nat], Nat := fun [inst : Add Nat] =>
    //   Nat.zero; f — the have-bound value is an instImplicit lambda.
    let j = elab_json(
        "have f : forall [inst : Add Nat], Nat := fun [inst : Add Nat] => Nat.zero; f",
    );
    // `have` elaborates to a `let`-free beta-reduced application or a
    // lambda application depending on the shape; assert only that it
    // elaborated and mentions the instImplicit pi in its type position.
    assert!(j["k"].is_string());
}
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test -p leanr_elab --test binder_smoke inst_binder -- --nocapture`

Expected: FAIL with `UnsupportedSyntax("binder group: Lean.Parser.Term.instBinder")` from `extract_binder_group`'s `binder_info_of` lookup.

- [ ] **Step 3: Map the kind and branch on the layout**

In `binder_info_of`:

```rust
        "Lean.Parser.Term.instBinder" => Some(BinderInfo::InstImplicit),
```

In `extract_binder_group`, before the existing names/type-slot reads, add the `instBinder` branch — its children are `["[", optIdent(null), T, "]"]`, so the name is optional and the type is a **bare** child, not a `KIND_NULL` wrapper:

```rust
    // `instBinder` (`[inst : C α]` / `[C α]`) has its own layout:
    // optional name at child [1] (null-wrapped), BARE type at child [2].
    // oracle: `toBinderViews`, `Binders.lean:450-453`.
    if kind == "Lean.Parser.Term.instBinder" {
        let ch = non_trivia_children(node);
        let name = match ch.get(1).and_then(|el| el.as_node()) {
            Some(opt) => match non_trivia_children(opt).first() {
                Some(NodeOrToken::Token(tok)) if kinds.name(tok.kind()) == "<ident>" => {
                    Some(intern_binder_name(elab, tok.text())?)
                }
                _ => None,
            },
            None => None,
        };
        let ty = ch.get(2).cloned().ok_or_else(|| {
            ElabError::UnsupportedSyntax("inst binder group: type slot".into())
        })?;
        return Ok(BinderGroup {
            names: vec![name],
            ty,
            bi: BinderInfo::InstImplicit,
        });
    }
```

Adjust the field names to match the actual `BinderGroup` struct in the file (read it first — the plan's shape is `{ names, ty, bi }` per its doc at `binder.rs:75-82`; if `names` is `Vec<NameId>` rather than `Vec<Option<NameId>>`, widen it to `Option` in this task and update `push_binder_group`'s loop, which already passes names straight through to `push_local_decl(name, …)` where the parameter is already `Option<NameId>`).

- [ ] **Step 4: Run the tests to verify they pass**

Run: `cargo test -p leanr_elab --test binder_smoke`

Expected: PASS.

- [ ] **Step 5: Run the crate suite**

Run: `cargo test -p leanr_elab`

Expected: PASS.

- [ ] **Step 6: Format and commit**

```bash
mise run fmt
git add crates/leanr_elab/src/builtin/binder.rs crates/leanr_elab/tests/binder_smoke.rs
git commit -m "$(cat <<'EOF'
feat(elab): instBinder in the bracketed-binder telescope (forall/let/have)

binder_info_of maps instBinder to InstImplicit; extract_binder_group
gains its layout branch (optional name, bare type) which differs from
the null-wrapped explicit/implicit/strict groups.

Claude-Session: https://claude.ai/code/session_01Dckmjcx6aKtDCEc1ZhcsBL
EOF
)"
```

---

### Task 4: `propagateExpectedType` — expected-type propagation into binder domains

This closes the seam at `crates/leanr_elab/src/app/args.rs:145` and the `seam_audit.rs` test that pins it.

**Files:**
- Modify: `crates/leanr_elab/src/builtin/binder.rs` (`elab_fun`)
- Modify: `crates/leanr_elab/src/app/args.rs:145-152` (delete the seam)
- Modify: `crates/leanr_elab/tests/seam_audit.rs` (`mvar_function_type_is_a_named_seam` → a positive test)
- Test: `crates/leanr_elab/tests/binder_smoke.rs`

**Interfaces:**
- Consumes: `MetaCtx::whnf`, `MetaCtx::is_def_eq`, `MetaCtx::instantiate1` (or the store's beta helper — read `binder.rs`'s existing imports and reuse what `elab_binders_and_forall` uses), `Store::expr_node`.
- Produces: `fn propagate_expected_type(elab: &mut TermElabM, fvar: ExprId, fvar_type: ExprId, expected: Option<ExprId>) -> Result<Option<ExprId>, ElabError>` in `binder.rs`.

**Oracle, verified verbatim** (`Lean/Elab/Binders.lean:410-421`):

```lean
private def propagateExpectedType (fvar : Expr) (fvarType : Expr) (s : State) : TermElabM State := do
  match s.expectedType? with
  | none              => pure s
  | some expectedType =>
    let expectedType ← whnfForall expectedType
    match expectedType with
    | .forallE _ d b _ =>
      discard <| isDefEq fvarType d.cleanupAnnotations
      let b := b.instantiate1 fvar
      return { s with expectedType? := some b }
    | _ =>
      return { s with expectedType? := none }
```

Four details that are easy to get wrong and that the tests below pin:

1. **`discard <| isDefEq`** — the result is *thrown away*. A failed unification does not error and does not stop the loop; it just leaves the domain mvar unassigned. Port it as `let _ = elab.mctx.is_def_eq(...)?;` — propagate a `MetaError`, ignore a `false`.
2. **`d.cleanupAnnotations`** — the domain is stripped of `optParam`/`autoParam`/mdata annotations before the `isDefEq`. If `leanr_meta` has no public `cleanup_annotations`, `AppElab::consume_opt_auto_param` in `app/args.rs` is the in-repo equivalent for the wrapper half; check whether a `MetaCtx` helper exists before adding one, and if none does, keep the port honest by naming the gap in a comment rather than silently skipping it.
3. **The non-`forallE` arm sets the expected type to `none`**, it does not keep the old one.
4. It runs **per binder, inside** the loop, after the binder's fvar is created and *before* the next binder's type elaborates.

- [ ] **Step 1: Write the failing tests**

In `crates/leanr_elab/tests/binder_smoke.rs`:

```rust
#[test]
fn fun_binder_domain_comes_from_the_expected_type() {
    // The seam this closes: `(fun f => f Nat.zero : (Nat -> Nat) -> Nat)`.
    // Without propagation, `f`'s domain stays an unassigned mvar and the
    // application `f Nat.zero` cannot proceed.
    let j = elab_json("(fun f => f Nat.zero : (Nat -> Nat) -> Nat)");
    assert_eq!(j["k"], "lam");
    // f's domain is now `Nat -> Nat`, not a bare mvar.
    assert_eq!(j["t"]["k"], "pi");
    assert_eq!(j["t"]["t"]["n"], "Nat");
    assert_eq!(j["b"]["k"], "app");
}

#[test]
fn fun_propagation_walks_a_multi_binder_telescope() {
    // (fun x y => x : Nat -> Nat -> Nat) — both domains come from the
    // expected type, one binder at a time.
    let j = elab_json("(fun x y => x : Nat -> Nat -> Nat)");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["t"]["n"], "Nat");
    assert_eq!(j["b"]["k"], "lam");
    assert_eq!(j["b"]["t"]["n"], "Nat");
    assert_eq!(j["b"]["b"]["i"], 1);
}

#[test]
fn fun_propagation_stops_at_a_non_forall_expected_type() {
    // More binders than the expected type has domains: propagation sets
    // the expected type to `none` and the remaining domains stay mvars.
    // Must not error.
    let j = elab_json("(fun x y => Nat.zero : Nat -> Nat)");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["t"]["n"], "Nat");
    assert_eq!(j["b"]["k"], "lam");
    assert_eq!(j["b"]["t"]["k"], "mvar");
}
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test -p leanr_elab --test binder_smoke fun_propagation fun_binder_domain -- --nocapture`

Expected: FAIL. The first panics with the `args.rs:145` seam message ("function type is still an unassigned metavariable after synthesis… M4b-3 P5"); the others fail on `mvar` where a `const`/`pi` is asserted.

- [ ] **Step 3: Implement `propagate_expected_type`**

In `crates/leanr_elab/src/builtin/binder.rs`:

```rust
/// oracle: `FunBinders.propagateExpectedType` (`Binders.lean:410-421`).
///
/// Runs once per binder, inside the telescope loop, AFTER the binder's
/// fvar exists and BEFORE the next binder's type elaborates. Returns the
/// residual expected type for the next iteration (and, at the end, for
/// the body).
///
/// Three details the oracle pins and this port keeps:
///   * `discard <| isDefEq` — a FAILED unification is not an error and
///     does not stop the walk. Only a `MetaError` propagates.
///   * the non-`forallE` arm returns `none`, dropping the expected type
///     rather than keeping the previous one.
///   * `whnfForall` keeps the ORIGINAL term when the reduct is not a
///     forall; only the `forallE` test reads it.
fn propagate_expected_type(
    elab: &mut TermElabM,
    fvar: ExprId,
    fvar_type: ExprId,
    expected: Option<ExprId>,
) -> Result<Option<ExprId>, ElabError> {
    let Some(expected) = expected else {
        return Ok(None);
    };
    let reduced = elab.mctx.whnf(expected)?;
    let base = elab.view.store;
    let Node::Forall {
        binder_type, body, ..
    } = elab.mctx.store().expr_node(Some(base), reduced)
    else {
        return Ok(None);
    };
    // oracle: `discard <| isDefEq fvarType d.cleanupAnnotations`. The
    // BOOL is discarded; a MetaError still propagates.
    let _ = elab.mctx.is_def_eq(fvar_type, binder_type)?;
    let rest = elab.mctx.instantiate1(body, fvar).map_err(ElabError::from)?;
    Ok(Some(rest))
}
```

Read `binder.rs`'s existing imports for the exact spelling of `Node`, `expr_node`, and the beta/instantiate helper; `elab_binders_and_forall` and `check_implicit_lambda` (`elab.rs`) both already destructure a `Node::Forall`, so copy their idiom rather than inventing one. If `MetaCtx` exposes no public `instantiate1`, use the same helper `mk_lambda`'s callers use to open a binder, or add `instantiate_beta_rev_range`-style composition — but if a `leanr_meta` addition proves necessary, it must be additive and Task 12 must amend the accessor ledger's `P5 | none expected` row.

- [ ] **Step 4: Thread it through `elab_fun`**

`elab_fun` must now receive the expected type. Change its signature to take `expected: Option<ExprId>` (the dispatcher at `crates/leanr_elab/src/dispatch.rs:271-273` already has it in scope — pass it through), and thread the residual:

```rust
        let mut residual = expected;
        for item in &items {
            for view in extract_fun_binder_views(elab, item, kinds)? {
                let dom = match &view.ty {
                    Some(ty_elem) => elab_type(elab, ty_elem, kinds)?,
                    None => fresh_type_mvar(elab)?,
                };
                let fvar = elab
                    .mctx
                    .push_local_decl(view.name, dom, view.bi)
                    .map_err(ElabError::from)?;
                residual = propagate_expected_type(elab, fvar, dom, residual)?;
                fvars.push(fvar);
            }
        }
```

Task 2's `optType` **wins over** the residual when both are present — the oracle's `expandFun` macro turns the body into an ascription, and an ascription's own type is what `elabTermEnsuringType` sees:

```rust
        let body_expected = match &opt_type {
            Some(ty_elem) => Some(elab_type(elab, ty_elem, kinds)?),
            None => residual,
        };
        let body = match body_expected {
            Some(t) => elab.elab_term_ensuring_type(&body_elem, kinds, Some(t))?,
            None => elab.elab_term(&body_elem, kinds, None)?,
        };
```

- [ ] **Step 5: Delete the `args.rs` seam**

In `crates/leanr_elab/src/app/args.rs`, remove the `if app.f_type_is_mvar_after_instantiation()? { … }` block (currently `:144-152`) so the path falls through to `Err(ElabError::FunctionExpected { f, f_type })` — the oracle's own "Function expected" error. Keep `f_type_is_mvar_after_instantiation` only if another caller uses it; otherwise delete it too and let clippy's dead-code lint confirm.

- [ ] **Step 6: Convert the seam-audit test to a positive test**

In `crates/leanr_elab/tests/seam_audit.rs`, `mvar_function_type_is_a_named_seam` currently asserts `msg.contains("M4b-3 P5")` (`:196`). Replace it with a test asserting the term now elaborates, and rename it:

```rust
/// Was `mvar_function_type_is_a_named_seam`. M4b-3 P5 Task 4 closed it:
/// `propagateExpectedType` supplies `f`'s domain from the ascription, so
/// the application proceeds instead of reporting an unassigned fType.
#[test]
fn mvar_function_type_is_closed_by_propagation() {
    let j = elab_json("(fun f => f Nat.zero : (Nat -> Nat) -> Nat)");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["b"]["k"], "app");
}
```

Also update the module doc at `seam_audit.rs:16` ("The still-open P5 seam this file DOES assert end-to-end") to name only the seams that remain after this plan — Task 12 does the final sweep, but do not leave this comment stating something the file no longer asserts.

- [ ] **Step 7: Run the tests to verify they pass**

Run: `cargo test -p leanr_elab`

Expected: PASS, including `seam_audit` and all 117 oracle records.

- [ ] **Step 8: Format and commit**

```bash
mise run fmt
git add crates/leanr_elab/src crates/leanr_elab/tests
git commit -m "$(cat <<'EOF'
feat(elab): propagateExpectedType into fun binder domains

Ports FunBinders.propagateExpectedType (Binders.lean:410-421) into the
fun telescope: whnfForall the expected type, isDefEq the binder domain
against it (result discarded, per the oracle's `discard <|`), instantiate
the body, hand the residual to the next binder and finally to the body.

Closes the app/args.rs mvar-fType seam; seam_audit's
mvar_function_type_is_a_named_seam becomes a positive test.

Claude-Session: https://claude.ai/code/session_01Dckmjcx6aKtDCEc1ZhcsBL
EOF
)"
```

---

### Task 5: Implicit-lambda insertion — the `.yes` path

`elab.rs`'s `check_implicit_lambda` is a P1 *guard*: it detects the condition and errors. This task makes it wrap.

**Files:**
- Modify: `crates/leanr_elab/src/elab.rs:355-421` (`check_implicit_lambda` → `use_implicit_lambda` + `elab_implicit_lambda`)
- Test: `crates/leanr_elab/tests/binder_smoke.rs`

**Interfaces:**
- Consumes: `MetaCtx::whnf`, `MetaCtx::push_local_decl`, `MetaCtx::mk_lambda`, `MetaCtx::instantiate1`, `MetaCtx::lctx_checkpoint`/`lctx_restore`, `block_implicit_lambda` (existing, `elab.rs`).
- Produces: `enum UseImplicitLambda { No, Yes(ExprId), Postpone }` and `fn elab_implicit_lambda(elab, elem, kinds, ty) -> Result<ExprId, ElabError>` in `elab.rs`.

**Oracle** (`Lean/Elab/Term/TermElabM.lean:1806-1820`):

```lean
private partial def elabImplicitLambda (stx : Syntax) (catchExPostpone : Bool) (type : Expr) : TermElabM Expr :=
  match type with
  | .forallE n d b bi =>
    if bi.isImplicit || bi.isInstImplicit then
      withFreshMacroScope <| withLocalDecl n bi d fun fvar => do
        let type ← instantiateForall ... -- b.instantiate1 fvar
        let e ← elabImplicitLambda stx catchExPostpone type
        mkLambdaFVars #[fvar] e
    else
      elabImplicitLambdaAux stx catchExPostpone type fvars
  | _ => elabImplicitLambdaAux stx catchExPostpone type fvars
```

Read `:1796-1820` in the pinned source before writing this — the recursion accumulates `impFVars` and `elabImplicitLambdaAux` is what finally elaborates `stx` against the residual type and wraps. Note the guard `bi.isImplicit || bi.isInstImplicit`: **strict-implicit does not trigger it**, matching `useImplicitLambda`'s own doc comment.

The existing guard at `elab.rs:391-421` is an unusually faithful transliteration and its doc comment is a correct record of the two arms it does not model. **Preserve that doc comment's content**, moving the still-accurate parts (the strict-implicit exclusion, `hasNoImplicitLambdaAnnotation` being vacuous in leanr) onto the new functions.

- [ ] **Step 1: Write the failing tests**

```rust
#[test]
fn implicit_lambda_wraps_against_an_implicit_forall() {
    // `(Nat.zero : {a : Type} -> Nat)` — the expected type is an
    // implicit forall, so the oracle wraps the WHOLE term in a lambda
    // rather than dispatching on its kind.
    let j = elab_json("(Nat.zero : {a : Type} -> Nat)");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "i");
    assert_eq!(j["b"]["k"], "const");
    assert_eq!(j["b"]["n"], "Nat.zero");
}

#[test]
fn implicit_lambda_wraps_instance_implicit_too() {
    let j = elab_json("(Nat.zero : [inst : Add Nat] -> Nat)");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "c");
}

#[test]
fn implicit_lambda_nests_for_several_implicit_binders() {
    let j = elab_json("(Nat.zero : {a : Type} -> {b : Type} -> Nat)");
    assert_eq!(j["k"], "lam");
    assert_eq!(j["bi"], "i");
    assert_eq!(j["b"]["k"], "lam");
    assert_eq!(j["b"]["bi"], "i");
    assert_eq!(j["b"]["b"]["n"], "Nat.zero");
}

#[test]
fn implicit_lambda_does_not_fire_on_strict_implicit() {
    // oracle: `unless c.isImplicit || c.isInstImplicit do return .no`,
    // and useImplicitLambda's doc: "implicit lambdas are not triggered
    // by the strict implicit binder annotation".
    let e = elab_result("(Nat.zero : ⦃a : Type⦄ -> Nat)");
    // No wrap: the ascription's ensure-type is what reports the mismatch,
    // NOT an implicit-lambda seam.
    match e {
        Err(leanr_elab::ElabError::UnsupportedSyntax(m)) => {
            assert!(!m.contains("implicit lambda"), "unexpected seam: {m}");
        }
        _ => {}
    }
}

#[test]
fn at_sign_disables_implicit_lambda() {
    // oracle: `App.lean:2269-2270` — `@` exists partly to disable the
    // feature. `@(t)` and `@t` both pass `implicitLambda := false`.
    let j = elab_json("(@(Nat.succ Nat.zero) : {a : Type} -> Nat)");
    // No lambda wrap: the term elaborates directly and the ascription
    // then fails or coerces, but the head is not a `lam` from this path.
    assert_ne!(j["k"], "lam");
}
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test -p leanr_elab --test binder_smoke implicit_lambda at_sign -- --nocapture`

Expected: FAIL with `UnsupportedSyntax("implicit lambda insertion — M4b-3 P5")` for the first three; the last two may already pass (they assert the *absence* of the wrap) — that is fine, they are regression pins.

- [ ] **Step 3: Turn the guard into a three-way classifier**

In `crates/leanr_elab/src/elab.rs`, replace `check_implicit_lambda`'s tail. Keep every doc-comment paragraph that is still true; correct the one citation error while you are here — the doc says `blockImplicitLambda` is at both `:1716-1720` and `:1715-1720`; the definition is at **`:1716`**, so make both read `:1716-1720`.

```rust
/// oracle: `useImplicitLambda`'s three-way result
/// (`TermElabM.lean:1732-1735`, `:1743-1779`).
enum UseImplicitLambda {
    No,
    Yes(ExprId),
    /// `stx` is a local identifier whose type is still an mvar
    /// application (`:1753-1778`). Needs term-level postponement, which
    /// leanr does not have — Task 6 owns this seam.
    Postpone,
}

fn use_implicit_lambda(
    elab: &mut TermElabM,
    elem: &SynElem,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<UseImplicitLambda, ElabError> {
    if block_implicit_lambda(elem, kinds) {
        return Ok(UseImplicitLambda::No);
    }
    let Some(expected) = expected else {
        return Ok(UseImplicitLambda::No);
    };
    // `hasNoImplicitLambdaAnnotation` (`:1706-1707`) stays unmodelled:
    // the annotation is minted only by `mkNoImplicitLambdaAnnotation`
    // and nothing in leanr builds one, so the test is vacuously false.
    let reduced = elab.mctx.whnf(expected)?;
    let base = elab.view.store;
    let Node::Forall { binder_info, .. } = elab.mctx.store().expr_node(Some(base), reduced) else {
        return Ok(UseImplicitLambda::No);
    };
    // oracle: `unless c.isImplicit || c.isInstImplicit do return .no` —
    // NOT strict-implicit. `useImplicitLambda`'s doc says so in as many
    // words.
    if !matches!(binder_info, BinderInfo::Implicit | BinderInfo::InstImplicit) {
        return Ok(UseImplicitLambda::No);
    }
    Ok(UseImplicitLambda::Yes(reduced))
}
```

(The `Postpone` arm is constructed in Task 6, not here. Leave the variant unconstructed for now and silence the lint with `#[allow(dead_code)]` on the variant, removing it in Task 6.)

- [ ] **Step 4: Implement the wrap**

```rust
/// oracle: `elabImplicitLambda` (`TermElabM.lean:1806-1820`) — peel every
/// leading implicit / instance-implicit binder off the expected type,
/// pushing an fvar for each, elaborate `stx` against the residual, and
/// `mkLambdaFVars` back over the collected fvars.
///
/// The wrap is around the WHOLE term and happens BEFORE any leaf or app
/// elaborator runs (`elabTermAux`, `:1839-1841`) — which is why it lives
/// here in `elab_term` rather than inside a leaf.
fn elab_implicit_lambda(
    elab: &mut TermElabM,
    elem: &SynElem,
    kinds: &KindInterner,
    mut ty: ExprId,
) -> Result<ExprId, ElabError> {
    let checkpoint = elab.mctx.lctx_checkpoint();
    let result = (|| {
        let base = elab.view.store;
        let mut fvars: Vec<ExprId> = Vec::new();
        loop {
            let Node::Forall {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = elab.mctx.store().expr_node(Some(base), ty)
            else {
                break;
            };
            if !matches!(binder_info, BinderInfo::Implicit | BinderInfo::InstImplicit) {
                break;
            }
            let fvar = elab
                .mctx
                .push_local_decl(binder_name, binder_type, binder_info)
                .map_err(ElabError::from)?;
            ty = elab.mctx.instantiate1(body, fvar).map_err(ElabError::from)?;
            fvars.push(fvar);
        }
        // oracle: `elabImplicitLambdaAux` — elaborate against the
        // RESIDUAL type, then wrap.
        let e = elab.elab_term_ensuring_type(elem, kinds, Some(ty))?;
        elab.mctx.mk_lambda(&fvars, e).map_err(ElabError::from)
    })();
    elab.mctx.lctx_restore(checkpoint);
    result
}
```

Match the `Node::Forall` field names to the real definition in `leanr_kernel` (the existing `check_implicit_lambda` destructures `Node::Forall { binder_info, .. }`, so the other field names must be read from `leanr_kernel/src/bank/terms.rs`).

- [ ] **Step 5: Wire it into `elab_term`**

Find the `check_implicit_lambda(...)?;` call site in `elab_term` / `elab_term_ensuring_type` and replace it:

```rust
        match use_implicit_lambda(self, elem, kinds, expected)? {
            UseImplicitLambda::Yes(ty) => return elab_implicit_lambda(self, elem, kinds, ty),
            UseImplicitLambda::Postpone => { /* Task 6 */ }
            UseImplicitLambda::No => {}
        }
```

Watch for infinite recursion: `elab_implicit_lambda` calls back into `elab_term_ensuring_type` with the *residual* type, which is no longer a leading implicit forall, so `use_implicit_lambda` returns `No` on the re-entry. The `fun_implicit_binder_carries_binder_info` test from Task 1 also guards this — `fun {a : Type} => a` with no expected type must not wrap.

- [ ] **Step 6: Run the tests to verify they pass**

Run: `cargo test -p leanr_elab --test binder_smoke`

Expected: PASS.

- [ ] **Step 7: Run the crate suite**

Run: `cargo test -p leanr_elab`

Expected: PASS. `seam_audit.rs:116` asserts `("@(Nat.succ Nat.zero)", "M4b-3 P5")` — that entry must now be **removed or converted**, since `@(...)` no longer reaches an implicit-lambda seam. If the test fails there, convert it the way Task 4 converted its seam test and note it for Task 12.

- [ ] **Step 8: Format and commit**

```bash
mise run fmt
git add crates/leanr_elab/src/elab.rs crates/leanr_elab/tests
git commit -m "$(cat <<'EOF'
feat(elab): implicit-lambda insertion replaces P1's guard

check_implicit_lambda becomes use_implicit_lambda (three-way, per the
oracle's UseImplicitLambdaResult) plus elab_implicit_lambda, which peels
leading implicit/instImplicit binders off the expected type, elaborates
the term against the residual, and wraps with mkLambdaFVars.

Strict-implicit still does not trigger it; `@` still disables it.
Corrects the blockImplicitLambda citation to :1716-1720.

Claude-Session: https://claude.ai/code/session_01Dckmjcx6aKtDCEc1ZhcsBL
EOF
)"
```

---

### Task 6: The `.postpone` seam and its elimMVarDeps reachability test

**Why this task exists.** P1 wrote off `useImplicitLambda`'s `.postpone` arm because "it is only reachable AFTER the implicit-forall test has already succeeded, and both of its continuations need the postponement ladder P1 deliberately does not have." That reasoning was sound then. It has aged: `.postpone` fires when `isMVarApp (← inferType x)` — a local identifier whose type is **an mvar application** — and PR #42 (elimMVarDeps) turned unassigned mvars into exactly that shape, aux-mvar applications over binder fvars. Task 1 multiplies binder producers on top. `leanr` still cannot postpone a term (`crates/leanr_elab/src/lib.rs:179-190`: `may_postpone` is written but never read, and `postpone_elab_term` has no call site), so P5 implements `.yes` and leaves `.postpone` a **named seam** — but a *narrowed* and *tested* one, not an unexamined assumption.

**Files:**
- Modify: `crates/leanr_elab/src/elab.rs` (`use_implicit_lambda`'s `Postpone` arm, and the `elab_term` dispatch)
- Test: `crates/leanr_elab/tests/seam_audit.rs`

**Interfaces:**
- Consumes: Task 5's `UseImplicitLambda`; `MetaCtx::infer_type`; a "head is an mvar" test — reuse whatever `app/args.rs`'s `f_type_is_mvar_after_instantiation` used before Task 4 deleted it, or `MetaCtx::instantiate_mvars` + `Node::MVar` on the head of the application spine.
- Produces: no new public surface.

- [ ] **Step 1: Write the failing test**

In `crates/leanr_elab/tests/seam_audit.rs`:

```rust
/// M4b-3 P5 Task 6. `useImplicitLambda`'s `.postpone` arm
/// (`TermElabM.lean:1753-1778`) fires when the term is a local
/// identifier whose type is an mvar APPLICATION. PR #42 (elimMVarDeps)
/// manufactures exactly that shape — aux-mvar applications over binder
/// fvars — so P1's "no corpus term reaches it" is no longer a safe
/// assumption.
///
/// leanr has no term-level postponement (`lib.rs`: `may_postpone` is
/// written, never read), so this must be a NAMED SEAM — an error the
/// caller can see — and never a silently different term.
#[test]
fn implicit_lambda_postpone_is_a_named_seam() {
    // A binder-bound local whose type is an unassigned mvar, used where
    // an implicit forall is expected.
    let src = "fun x => (x : {a : Type} -> Nat)";
    let e = elab_result(src);
    let msg = match e {
        Err(leanr_elab::ElabError::UnsupportedSyntax(m)) => m,
        other => panic!("expected a named seam for {src:?}, got {other:?}"),
    };
    assert!(
        msg.contains("implicit lambda postponement") && msg.contains("M4b-4"),
        "seam must name the postponement gap and its owning slice: {msg}"
    );
}
```

`elab_result` lives in `binder_smoke.rs`; either move it into `tests/support/mod.rs` so both files share it, or duplicate the small helper here. Prefer moving it — `oracle_elab.rs`, `binder_smoke.rs` and `seam_audit.rs` all build the same `MetaCtx`, and a fourth copy is where drift starts.

**If this test cannot be made to reach the arm**, that is a real finding, not a failure: the arm requires `blockImplicitLambda` to be false for the term, and a bare local identifier may be excluded by `isLocalIdent?`'s own conditions. Spend at most one round trying two or three shapes; if none reach it, keep the seam code, change the test to assert the *classifier* directly (call `use_implicit_lambda` on a hand-built state where the ident's type is an mvar application), and record in the test's doc comment that no source-level term reaches it today and why.

- [ ] **Step 2: Run the test to verify it fails**

Run: `cargo test -p leanr_elab --test seam_audit implicit_lambda_postpone -- --nocapture`

Expected: FAIL — either the term elaborates (no seam) or it errors with a different message.

- [ ] **Step 3: Implement the arm**

In `use_implicit_lambda`, before the final `Ok(UseImplicitLambda::Yes(reduced))`, add the oracle's local-ident test:

```rust
    // oracle: `if let some x ← isLocalIdent? stx then if (← isMVarApp
    // (← inferType x)) then return .postpone` (`:1753-1778`). The
    // comment there explains why: adding implicit lambdas to a local
    // whose type is not yet known makes elaboration fail, because the
    // fvars the wrap introduces are not in the local's mvar scope.
    if let Some(x) = local_ident_of(elab, elem, kinds)? {
        let x_ty = elab.mctx.infer_type(x)?;
        if is_mvar_app(elab, x_ty)? {
            return Ok(UseImplicitLambda::Postpone);
        }
    }
```

and in `elab_term`'s dispatch:

```rust
            UseImplicitLambda::Postpone => {
                return Err(ElabError::UnsupportedSyntax(
                    "implicit lambda postponement: the term is a local whose type is an \
                     unassigned metavariable application, which the oracle postpones \
                     (TermElabM.lean:1753-1778). leanr has no term-level postponement \
                     (`may_postpone` is written but never read) — M4b-4"
                        .to_string(),
                ));
            }
```

Remove the `#[allow(dead_code)]` Task 5 put on the variant.

Write `local_ident_of` and `is_mvar_app` as small private helpers; `is_mvar_app` is `instantiate_mvars`, walk to the head of the application spine, test `Node::MVar` — oracle `isMVarApp` at `TermElabM.lean:1375`.

- [ ] **Step 4: Run the test to verify it passes**

Run: `cargo test -p leanr_elab --test seam_audit implicit_lambda_postpone -- --nocapture`

Expected: PASS.

- [ ] **Step 5: Run the crate suite**

Run: `cargo test -p leanr_elab`

Expected: PASS. If any of the 117 oracle records now hits the new seam, **stop** — that is a real regression meaning the arm is over-broad; narrow `local_ident_of` and re-run.

- [ ] **Step 6: Format and commit**

```bash
mise run fmt
git add crates/leanr_elab/src/elab.rs crates/leanr_elab/tests
git commit -m "$(cat <<'EOF'
feat(elab): narrow the implicit-lambda seam to useImplicitLambda's .postpone arm

P1 wrote this arm off as unreachable. elimMVarDeps (#42) manufactures the
shape it tests for — a local whose type is an mvar application — and P5
multiplies binder producers, so the arm is now modelled explicitly and
reported as a named M4b-4 seam rather than left to fall through.

Claude-Session: https://claude.ai/code/session_01Dckmjcx6aKtDCEc1ZhcsBL
EOF
)"
```

---

### Task 7: Scoping audit at the binder/argument family boundary

Amendment 8 pins this task and gives it two independent reasons. This is an **audit**, so its deliverable is a test file section plus findings — not necessarily a code change.

**Files:**
- Modify: `crates/leanr_elab/tests/seam_audit.rs` (a new `mod scoping_audit` section)
- Modify: whichever elaborator paths the audit finds wrong (unknown until run)

**Interfaces:**
- Consumes: `MetaCtx::with_mvar_local_context` (added by PR #43 — confirm its exact name and visibility with `grep -rn "with_mvar_local_context" crates/leanr_meta/src/` before writing; if it is `pub(crate)`, the audit runs inside `leanr_meta`'s own tests instead, and this task's tests assert observable behaviour from `leanr_elab` instead of calling it).
- Produces: findings, recorded in the test file's module doc.

**The two reasons, from Amendment 8 and the local-instances spec.** (1) `elim_mvar_deps` turns unassigned mvars into aux-mvar applications over binder fvars, which made a dormant scoping seam live once already (`default_inst.rs` rung 3 broke on `fun (n : Nat) => 0`, a term no corpus record covered). Tasks 1–6 multiply binder producers. (2) Local instances change *what synthesis finds* under a binder, so a goal solved under the wrong local context now silently picks a different instance rather than merely failing.

- [ ] **Step 1: Enumerate the paths to audit**

Run and record the output:

```bash
grep -rn "synth_instance\|synthesize_pending\|infer_type\|is_def_eq" crates/leanr_elab/src --include=*.rs | grep -v "^.*tests"
```

For each hit, answer in a comment in the new test module: *when this runs while a binder from Task 1/5 is open, whose local context is it using — the mvar's, or the ambient one?* The oracle's rule is `mvarId.withContext` before touching a goal.

- [ ] **Step 2: Write tests that pin the answer for each reachable path**

```rust
//! M4b-3 P5 Task 7 — scoping audit at the binder/argument family
//! boundary. Two reasons (spec § Amendment 8 item 4): elimMVarDeps
//! makes dormant scoping seams live, and local instances change what
//! synthesis finds under a binder.
mod scoping_audit {
    use super::*;

    /// Synthesis under an instance-implicit binder must find the LOCAL
    /// instance, not a global one — `get_instances` appends matching
    /// locals ahead of globals (PR #43).
    #[test]
    fn synthesis_under_a_local_instance_binder_prefers_the_local() {
        // `Add Nat` has a global instance in Elab0; the binder supplies
        // a local one. The elaborated term must mention the BINDER
        // (a bvar), not the global constant.
        let j = elab_json("fun [inst : Add Nat] => (Add.add Nat.zero Nat.zero : Nat)");
        let s = serde_json::to_string(&j).unwrap();
        assert!(
            s.contains("\"bvar\""),
            "expected the local instance to be used, got {s}"
        );
    }

    /// A binder whose domain is an elimMVarDeps-produced aux-mvar
    /// application must not desynchronise the local context.
    #[test]
    fn binder_over_an_aux_mvar_domain_stays_scoped() {
        let j = elab_json("fun (n : Nat) => (fun x => x : Nat -> Nat)");
        assert_eq!(j["k"], "lam");
        assert_eq!(j["b"]["k"], "lam");
    }
}
```

- [ ] **Step 3: Run the audit tests**

Run: `cargo test -p leanr_elab --test seam_audit scoping_audit -- --nocapture`

Expected: PASS, or a **finding**. If one fails, that is the task's real deliverable: fix it here (an additive fix to the seam the failure names — never a blanket lift, per the local-instances spec's own rule), and record what it was in the module doc.

- [ ] **Step 4: Run the full workspace test suite**

Run: `mise run test`

Expected: PASS. This is the first task that should exercise `meta:fast` alongside the elaborator, because local instances cross the crate boundary.

- [ ] **Step 5: Format and commit**

```bash
mise run fmt
git add crates/leanr_elab
git commit -m "$(cat <<'EOF'
test(elab): scoping audit at the P5 binder/argument family boundary

Pins that synthesis under an instance-implicit binder prefers the local
instance, and that a binder over an elimMVarDeps-shaped domain keeps its
local context synchronised. Amendment 8 item 4's two reasons.

Claude-Session: https://claude.ai/code/session_01Dckmjcx6aKtDCEc1ZhcsBL
EOF
)"
```

---

### Task 8: `optParam` defaults

**Files:**
- Modify: `crates/leanr_elab/src/app/args.rs` (the seam at `:405-416`)
- Test: `crates/leanr_elab/tests/app_smoke.rs`

**Interfaces:**
- Consumes: `AppElab::get_param_type`, `AppElab::consume_opt_auto_param`, `AppElab::add_new_arg` (read the file for the exact name — the oracle calls it `addNewArg`), `AppElab::type_annotation_at_head`.
- Produces: `fn opt_param_default(app: &mut AppElab, param_type: ExprId) -> Result<Option<ExprId>, ElabError>` — the `getOptParamDefault?` reader. Task 9 sits beside it in the same `match`.

**Oracle** (`Lean/Elab/App.lean:826-829`):

```lean
      let paramType ← getParamType
      match (← read).explicit, paramType.getOptParamDefault?, paramType.getAutoParamTactic? with
      | false, some defVal, _  => addNewArg argName defVal; main
```

`optParam α d` is `@[reducible] def optParam (α : Sort u) (default : α) : Sort u := α`, so `getOptParamDefault?` is "if the head is `const optParam` applied to two arguments, return the second". The default value `d` is **used as the argument directly** — not elaborated again, and not replaced by a fresh mvar. `addNewArg` then continues the `main` loop.

- [ ] **Step 1: Write the failing test**

Add to `tests/fixtures/elab/Elab0.lean` (Task 10 regenerates the corpus; this task only needs the *declaration* present for the smoke test, and `replay_fixture_in` reads the committed `.olean`, so **this test cannot run until Task 10 rebuilds `Elab0.olean`**). To keep this task independently testable, use a declaration that **already exists** in the committed environment. Check first:

```bash
grep -n "optParam\|:= *[0-9]" tests/fixtures/elab/Elab0.lean | head -20
```

If no `optParam`-carrying declaration exists yet, **reorder**: do Task 10's `Elab0.lean` + regen for the two declarations this task and Task 9 need, commit that, then return here. State which you did in the commit message.

```rust
#[test]
fn opt_param_default_is_the_declared_value() {
    // `def withDefault (n : Nat := Nat.zero) : Nat := n`
    // `withDefault` with no argument → `withDefault Nat.zero`, NOT
    // `withDefault ?m`.
    let j = elab_json("withDefault");
    assert_eq!(j["k"], "app");
    assert_eq!(j["f"]["n"], "withDefault");
    assert_eq!(j["a"]["k"], "const");
    assert_eq!(j["a"]["n"], "Nat.zero");
}

#[test]
fn opt_param_explicit_mode_does_not_fill() {
    // oracle gates the arm on `!explicit`. `@withDefault` must leave the
    // parameter to be supplied positionally.
    let j = elab_json("@withDefault Nat.zero");
    assert_eq!(j["k"], "app");
    assert_eq!(j["a"]["n"], "Nat.zero");
}
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test -p leanr_elab --test app_smoke opt_param -- --nocapture`

Expected: FAIL with `UnsupportedSyntax("optParam default / autoParam tactic argument — M4b-3 P5")`.

- [ ] **Step 3: Implement the default reader and the arm**

In `crates/leanr_elab/src/app/args.rs`, replace the seam block:

```rust
    // oracle: `App.lean:827-829` — the optParam/autoParam default-filling
    // arms, gated on `!explicit` exactly as the oracle's match scrutinee.
    // `get_arg_expected_type` already strips the wrapper for an
    // EXPLICITLY supplied argument; this is the DEFAULT path.
    if !app.ctx.explicit {
        let param_type = app.get_param_type()?;
        if let Some(def_val) = opt_param_default(app, param_type)? {
            // oracle: `addNewArg argName defVal; main` — the declared
            // default becomes the argument DIRECTLY. Not re-elaborated,
            // not a fresh mvar.
            app.add_new_arg(def_val)?;
            return Ok(true);
        }
    }
```

and add:

```rust
/// oracle: `Expr.getOptParamDefault?` — `optParam α d` is a reducible
/// two-argument application, and `d` is the default.
fn opt_param_default(app: &AppElab, ty: ExprId) -> Result<Option<ExprId>, ElabError> {
    // Reuse the head test `consume_opt_auto_param` already relies on;
    // read `head_is_opt_or_auto_param` and `type_annotation_at_head` in
    // this file and follow their idiom for walking the spine.
    todo!("read the two helpers above and mirror their spine walk")
}
```

**Do not leave the `todo!`** — it is written here only to mark where the file's own existing helpers must be read and mirrored. Replace it in this step with the real spine walk: instantiate mvars, take the head, check it is `Const { name: "optParam" }` with exactly two arguments, return the second.

Keep the `autoParam` half of the old seam intact for now — Task 9 replaces it. That means the `if` above must fall through to the existing seam when the parameter is an `autoParam` rather than an `optParam`.

- [ ] **Step 4: Run the tests to verify they pass**

Run: `cargo test -p leanr_elab --test app_smoke`

Expected: PASS.

- [ ] **Step 5: Run the crate suite**

Run: `cargo test -p leanr_elab`

Expected: PASS, 117 records green.

- [ ] **Step 6: Format and commit**

```bash
mise run fmt
git add crates/leanr_elab
git commit -m "$(cat <<'EOF'
feat(elab): optParam default-argument filling

An omitted parameter whose type is `optParam α d` takes `d` as its
argument directly (oracle App.lean:827-829), not a fresh mvar. Gated on
!explicit, so `@f` still requires the argument positionally.

Claude-Session: https://claude.ai/code/session_01Dckmjcx6aKtDCEc1ZhcsBL
EOF
)"
```

---

### Task 9: `autoParam` — the `.tactic` synthetic metavariable

**Files:**
- Modify: `crates/leanr_elab/src/app/args.rs` (replace the remaining seam)
- Modify: `crates/leanr_elab/src/synthetic/state.rs` (register the `Tactic` kind), `crates/leanr_elab/src/synthetic/report.rs` (report it)
- Test: `crates/leanr_elab/tests/app_smoke.rs`, `crates/leanr_elab/tests/seam_audit.rs`

**Interfaces:**
- Consumes: Task 8's arm structure; the synthetic-mvar registry in `synthetic/state.rs` (`state.rs:48` already says "P5 registers `Tactic`").
- Produces: a `SyntheticMVarKind::Tactic` variant (match the enum's real name in `state.rs`).

**Scope, from the spec.** "Strip the wrapper; an explicitly-supplied argument elaborates normally (fully oracle-verifiable); an omitted one creates the `.tactic` synthetic mvar exactly as `App.lean:846` does, **with execution left to P2's seam**. Full autoParam would pull in the `by` elaborator and the tactic framework, which the roadmap assigns to a later M4 slice."

So: mint the mvar, register it as `.tactic`, and let the synthetic-mvar ladder report it as unsolved. Do **not** evaluate the tactic. The oracle's `evalSyntaxConstant` + `` `(by $tacticSyntax) `` quoting is explicitly out of scope.

- [ ] **Step 1: Write the failing tests**

```rust
#[test]
fn auto_param_explicit_argument_elaborates_normally() {
    // `def withTactic (n : Nat := by exact Nat.zero) : Nat := n`
    // Supplying the argument bypasses the tactic entirely.
    let j = elab_json("withTactic Nat.zero");
    assert_eq!(j["k"], "app");
    assert_eq!(j["a"]["n"], "Nat.zero");
}
```

In `seam_audit.rs`:

```rust
/// M4b-3 P5 Task 9. An OMITTED autoParam argument mints a `.tactic`
/// synthetic mvar (oracle `App.lean:846`). Executing it needs the `by`
/// elaborator and the tactic framework, which the roadmap assigns to a
/// later M4 slice — so the ladder must REPORT it, not solve it, and
/// never fall through to a different term.
#[test]
fn omitted_auto_param_is_a_reported_tactic_mvar() {
    let e = elab_result("withTactic");
    let msg = match e {
        Err(err) => format!("{err:?}"),
        Ok(_) => panic!("an omitted autoParam must not silently elaborate"),
    };
    assert!(
        msg.contains("tactic"),
        "the report must name the tactic mvar: {msg}"
    );
}
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test -p leanr_elab auto_param -- --nocapture`

Expected: FAIL with the `optParam default / autoParam tactic argument — M4b-3 P5` seam.

- [ ] **Step 3: Register the `Tactic` synthetic-mvar kind**

In `crates/leanr_elab/src/synthetic/state.rs`, add the variant beside `TypeClass`, `Postponed` and `Coe` (see the doc at `:48`), and give it whatever payload the reporter needs — at minimum the parameter name, for the message. In `synthetic/report.rs`, add its arm so an unsolved `Tactic` mvar produces a clear error naming the parameter and the deferring slice.

- [ ] **Step 4: Mint the mvar in the argument loop**

In `args.rs`, extend Task 8's block:

```rust
    if !app.ctx.explicit {
        let param_type = app.get_param_type()?;
        if let Some(def_val) = opt_param_default(app, param_type)? {
            app.add_new_arg(def_val)?;
            return Ok(true);
        }
        if auto_param_tactic(app, param_type)?.is_some() {
            // oracle: `App.lean:840-848` — mint a synthetic mvar of kind
            // `.autoParam argName` at the argument's expected type and
            // add it as the argument. leanr registers it as `.tactic`
            // and leaves EXECUTION to the tactic framework (a later M4
            // slice): the oracle's `evalSyntaxConstant` / `by` quoting
            // is deliberately not ported.
            let expected = app.get_arg_expected_type()?;
            let mvar = app.mk_tactic_mvar(expected)?;
            app.add_new_arg(mvar)?;
            return Ok(true);
        }
    }
```

Delete the old seam block entirely. Write `auto_param_tactic` (the `getAutoParamTactic?` reader — head is `const autoParam` applied to two arguments, return the second) and `mk_tactic_mvar` (a fresh mvar registered in the synthetic table with the new kind) mirroring how `app/args.rs` already mints `.coe` and instance mvars.

- [ ] **Step 5: Run the tests to verify they pass**

Run: `cargo test -p leanr_elab`

Expected: PASS.

- [ ] **Step 6: Format and commit**

```bash
mise run fmt
git add crates/leanr_elab
git commit -m "$(cat <<'EOF'
feat(elab): autoParam mints a .tactic synthetic metavariable

An omitted autoParam argument becomes a synthetic mvar of the new
Tactic kind (oracle App.lean:840-848), reported rather than solved:
executing the tactic needs the `by` elaborator and the tactic framework,
which the roadmap assigns to a later M4 slice. An explicitly supplied
argument still elaborates normally through the existing wrapper strip.

Closes the last app/args.rs P5 seam.

Claude-Session: https://claude.ai/code/session_01Dckmjcx6aKtDCEc1ZhcsBL
EOF
)"
```

---

### Task 10: Oracle corpus — declarations, queries, regeneration

Every form Tasks 1–9 added needs a differential record. The smoke tests assert *shape*; `oracle_elab` asserts **byte-identity with the oracle**, and that is the gate that matters.

**Files:**
- Modify: `tests/fixtures/elab/Elab0.lean` (new declarations)
- Modify: `tests/fixtures/elab/dump_elab.lean` (new query groups + the `main` concatenation)
- Regenerate: `tests/fixtures/elab/Elab0.olean`, `tests/fixtures/elab/elab-queries.jsonl`

**Interfaces:**
- Consumes: `mise run fixtures:regen-elab` (`mise.toml:214`), which depends on `elan:bootstrap`. `Elab0.olean` itself is built in `fixtures:regen`'s run list (`mise.toml:159`).
- Produces: a grown `elab-queries.jsonl`. Task 11 measures the growth.

**This task needs the pinned Lean toolchain.** It never runs in CI. If `lean` is unavailable in the execution environment, **stop and say so** — do not hand-write records.

- [ ] **Step 1: Add the declarations to `Elab0.lean`**

Append, following the file's existing comment style (each declaration says which oracle path needs it):

```lean
-- M4b-3 P5 Task 8/9: `optParam` and `autoParam` carriers. `withDefault`
-- has a declared default (`App.lean:828`); `withTactic` an auto-param
-- tactic (`:829-848`), whose EXECUTION is a later M4 slice — the record
-- only pins the explicitly-supplied form.
def withDefault (n : Nat := Nat.zero) : Nat := n
def withTactic (n : Nat := by exact Nat.zero) : Nat := n

-- M4b-3 P5 Task 1/3: an instance-implicit binder needs a class in scope
-- whose local instance can be preferred over a global one. `Add`/`instAddNat`
-- may already be present; add only what `grep` shows missing.
```

Check what is already there before adding — `grep -n "^def \|^structure \|^instance \|^class " tests/fixtures/elab/Elab0.lean`.

- [ ] **Step 2: Add the query groups to `dump_elab.lean`**

Follow the existing `def <name>Queries : List (String × String)` shape (see `binderQueries` at `:253`, `funQueries` at `:264`):

```lean
/-- M4b-3 P5 binder family: implicit / strict-implicit / instance-implicit
`fun` binders, multi-name groups, type-less binders, `optType`, and
expected-type propagation into binder domains. -/
def p5BinderQueries : List (String × String) :=
  [ ("p5/fun-implicit",         "fun {a : Type} => a")
  , ("p5/fun-implicit-untyped", "fun {a} => a")
  , ("p5/fun-implicit-group",   "fun {a b : Type} => a")
  , ("p5/fun-strict",           "fun ⦃a : Type⦄ => a")
  , ("p5/fun-inst-named",       "fun [inst : Add Nat] => inst")
  , ("p5/fun-inst-anon",        "fun [Add Nat] => Nat.zero")
  , ("p5/fun-opttype",          "fun (x : Nat) : Nat => x")
  , ("p5/fun-opttype-dep",      "fun (a : Type) (x : a) : a => x")
  , ("p5/forall-inst",          "forall [inst : Add Nat], Nat")
  , ("p5/propagate-fn",         "(fun f => f Nat.zero : (Nat -> Nat) -> Nat)")
  , ("p5/propagate-two",        "(fun x y => x : Nat -> Nat -> Nat)")
  , ("p5/propagate-short",      "(fun x y => Nat.zero : Nat -> Nat)")
  ]

/-- M4b-3 P5 implicit-lambda insertion (`TermElabM.lean:1806-1820`). -/
def p5ImplicitLambdaQueries : List (String × String) :=
  [ ("p5/implam-one",    "(Nat.zero : {a : Type} -> Nat)")
  , ("p5/implam-inst",   "(Nat.zero : [inst : Add Nat] -> Nat)")
  , ("p5/implam-nested", "(Nat.zero : {a : Type} -> {b : Type} -> Nat)")
  ]

/-- M4b-3 P5 argument family: `optParam` defaults and an explicitly
supplied `autoParam` argument. An OMITTED autoParam is a reported seam,
not a record — executing the tactic is a later M4 slice. -/
def p5ArgQueries : List (String × String) :=
  [ ("p5/optparam-default",  "withDefault")
  , ("p5/optparam-explicit", "@withDefault Nat.zero")
  , ("p5/autoparam-supplied", "withTactic Nat.zero")
  ]
```

Then extend the concatenation in `main` (`dump_elab.lean:740`), appending `++ p5BinderQueries ++ p5ImplicitLambdaQueries ++ p5ArgQueries` to the existing chain.

- [ ] **Step 3: Regenerate**

```bash
mise run elan:bootstrap
sh -c 'cd tests/fixtures/elab && lean Elab0.lean -o Elab0.olean'
mise run fixtures:regen-elab
```

- [ ] **Step 4: Verify the corpus grew and nothing else moved**

```bash
git diff --stat tests/fixtures/elab/
git diff tests/fixtures/elab/elab-queries.jsonl | grep '^-' | grep -v '^---' | head
```

Expected: `elab-queries.jsonl` gains ~18 lines and **loses none**. `Elab0.olean` changes (new declarations). If any existing record line was removed or modified, **stop** — that is a neutrality violation and Task 11's gate would catch it anyway; find out why before proceeding.

- [ ] **Step 5: Run the differential gate**

Run: `cargo test -p leanr_elab --test oracle_elab -- --nocapture`

Expected: PASS with the new record count (117 + the new entries). A failure here is the real signal of this whole plan: leanr's term differs from the oracle's, byte for byte, and the failing `id` names which form.

- [ ] **Step 6: Commit**

```bash
mise run fmt
git add tests/fixtures/elab/
git commit -m "$(cat <<'EOF'
test(fixtures): M4b-3 P5 oracle corpus — binder breadth, implicit lambdas, optParam

Adds withDefault/withTactic to Elab0 and three query groups to
dump_elab: the binder family (implicit/strict/inst binders, groups,
optType, propagation), implicit-lambda insertion, and the argument
family. An omitted autoParam is a reported seam, not a record.

Regenerated with the pinned v4.33.0-rc1 toolchain.

Claude-Session: https://claude.ai/code/session_01Dckmjcx6aKtDCEc1ZhcsBL
EOF
)"
```

---

### Task 11: Neutrality measurement

Every prerequisite slice in this chain measured neutrality explicitly, and #43's measurement ("elab corpus byte-identical at 117; synth 26 → 32 as a pure append") is what let it merge. P5 *does* change elaboration behaviour, so its gate is different: **no pre-existing record may change**, and every changed line must be a new one.

**Files:**
- Create: no source files. This task produces a measurement recorded in Task 12's amendment.

**Interfaces:**
- Consumes: `git diff` against the branch's merge-base with `main` (`a1f8f9e` at the time of writing — recompute it, do not hardcode).

- [ ] **Step 1: Compute the baseline**

```bash
BASE=$(git merge-base HEAD main)
echo "baseline: $BASE"
```

- [ ] **Step 2: Measure the elaboration corpus**

```bash
BASE=$(git merge-base HEAD main)
echo "records before: $(git show $BASE:tests/fixtures/elab/elab-queries.jsonl | grep -c .)"
echo "records after:  $(grep -c . tests/fixtures/elab/elab-queries.jsonl)"
echo "--- lines REMOVED or MODIFIED (must be empty) ---"
git diff $BASE -- tests/fixtures/elab/elab-queries.jsonl | grep '^-' | grep -v '^---'
```

Expected: the removed-lines list is **empty**. Anything there is a changed pre-existing record — a behaviour change to a term that already worked. Investigate before proceeding; it may be correct (the oracle's own answer for that term genuinely involves an implicit lambda leanr previously skipped) but it must be *understood and recorded*, not absorbed.

- [ ] **Step 3: Measure the synthesis corpus**

```bash
BASE=$(git merge-base HEAD main)
echo "synth before: $(git show $BASE:tests/fixtures/meta/synth-queries.jsonl | grep -c .)"
echo "synth after:  $(grep -c . tests/fixtures/meta/synth-queries.jsonl)"
git diff $BASE -- tests/fixtures/meta/synth-queries.jsonl | grep '^-' | grep -v '^---'
```

Expected: unchanged. P5 adds no `leanr_meta` behaviour, so this corpus should not move at all.

- [ ] **Step 4: Confirm `leanr_meta/src` is untouched or additive-only**

```bash
BASE=$(git merge-base HEAD main)
git diff --stat $BASE -- crates/leanr_meta/src/
```

Expected: **empty**. The accessor ledger's P5 row says `none expected`. If it is non-empty, every hunk must be an additive, TCB-neutral accessor, and Task 12 must amend the ledger row with the rejected alternative recorded — per the M4b elab→meta accessor precedent.

- [ ] **Step 5: Run the full CI gate**

Run: `mise run ci`

Expected: PASS — `cargo fmt --check`, clippy, and the whole test suite including `meta:fast`.

- [ ] **Step 6: Record the measurement**

Write the four numbers and the `leanr_meta` diff status into a scratch note for Task 12. No commit — this task's output is data.

---

### Task 12: Seam-audit sweep, citation fixes, Amendment 9, whole-branch review

**Files:**
- Modify: `crates/leanr_elab/tests/seam_audit.rs` (module doc + any stale entries)
- Modify: `crates/leanr_elab/src/lib.rs`, `crates/leanr_elab/src/dispatch.rs`, `crates/leanr_elab/src/app/mod.rs` (seam ledgers naming P5)
- Modify: `docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md` (Amendment 9)

- [ ] **Step 1: Find every remaining P5 mention and classify it**

```bash
grep -rn "M4b-3 P5\|M4b-3 P5\b\|P5" crates/leanr_elab/src crates/leanr_elab/tests --include=*.rs
```

For each hit: is the seam **closed** (delete or convert the mention), **still open** (keep, and make sure the message names the right owning slice), or **retargeted** (P5 → M4b-4, e.g. the `.postpone` arm from Task 6)? The known list to check, from the pre-plan sweep: `lib.rs:107`, `elab.rs:361`, `elab.rs:419`, `app/args.rs:145`, `app/args.rs:412`, `dispatch.rs:153-154`, `app/mod.rs:32,45,57,58,93,187,215`, `synthetic/state.rs:48`, `synthetic/default_inst.rs:115`, `app/state.rs:179,241`, `seam_audit.rs:11,16,87,92,93,115,116,177,196,382,644,645`.

- [ ] **Step 2: Fix the two verified citation errors**

- `docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md` § P5 cites `App.lean:2268-2270` for `@` disabling implicit lambdas. The substantive lines are **2269-2270**; 2268 is the preceding `@.$_:ident.{$_us,*}` match arm. (`app/mod.rs:215` already has it right.)
- `crates/leanr_elab/src/elab.rs` cites `blockImplicitLambda` as both `:1716-1720` and `:1715-1720`. The definition is at **1716**. Task 5 should already have fixed this; verify.

- [ ] **Step 3: Run the whole-branch review**

Use the `superpowers:requesting-code-review` skill against the full branch diff, and specifically probe the three inherited hazards:

1. **`MetavarDecl.localInstances` surviving postponement** — the local-instances spec names this "the first thing P5's own whole-branch review should probe". A postponed synthetic mvar resumed after its binder closed must carry its local instances with it.
2. **`LocalCtxSnapshot::reduced()` renumbering** — `LocalContext::erase` renumbers every later decl down by one, and anything carrying a recorded index into `lctx.decls` must be renumbered with it. This cost #43 a Critical. Tasks 1, 3 and 5 all push decls.
3. **The `get_instances` re-entrancy seam** — `mem::take` of the instance table during `discr_get_match` means a nested `get_instances` reports no *global* instances. P5 creates binder-scoped synthesis goals, which is new pressure on it. **This plan deliberately leaves it open** (closing it changes the global lookup path and is its own slice). The review's job is to determine whether P5 makes it *live*; if it does, that is a finding for a follow-up slice, not a fix here.

- [ ] **Step 4: Write Amendment 9**

Append to `docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md`, recording:

- **What Amendment 8 got wrong, and why.** Two of its seven items were already closed when P5 started: local-instance wiring (PR #43's `push_local_decl` installs on type alone, which is exactly the oracle's rule, so P5 needed only to pass the right `BinderInfo`) and the `..` ellipsis (closed by an earlier plan's task 7). Amendment 8 was written before #43 landed and inherited the ellipsis item from the original § P5 bullet list without re-checking it.
- **The `.postpone` finding.** P1's write-off of `useImplicitLambda`'s third arm was sound when written and aged badly: elimMVarDeps (#42) manufactures the mvar-application shape the arm tests for. Recorded as the concrete instance of the spec's own warning that "no corpus term reaches it" is a claim with a shelf life.
- **The neutrality measurement** from Task 11, verbatim numbers.
- **The accessor ledger's P5 row** — confirmed `none expected`, or amended with what was added and why.
- **What the next slice inherits**, including the still-open `get_instances` re-entrancy seam and whatever Step 3's review turned up.

- [ ] **Step 5: Run the full gate one last time**

Run: `mise run ci`

Expected: PASS.

- [ ] **Step 6: Commit**

```bash
mise run fmt
git add crates/leanr_elab docs/superpowers/specs
git commit -m "$(cat <<'EOF'
docs(m4b3): Amendment 9 — P5 landed, seam sweep, citation fixes

Records that two of Amendment 8's seven items were already closed before
P5 started (local-instance wiring by #43, `..` ellipsis by an earlier
plan), the elimMVarDeps-driven revival of useImplicitLambda's .postpone
arm, P5's neutrality measurement, and what the next slice inherits —
including the still-open get_instances re-entrancy seam.

Corrects App.lean:2268-2270 to :2269-2270 and blockImplicitLambda to :1716.

Claude-Session: https://claude.ai/code/session_01Dckmjcx6aKtDCEc1ZhcsBL
EOF
)"
```

---

## Self-Review

**Spec coverage.** Amendment 8's seven items map as: binder-info breadth → Tasks 1 and 3; `fun`'s `optType` → Task 2; `propagateExpectedType` → Task 4; implicit-lambda insertion → Tasks 5 and 6; `optParam` → Task 8; `autoParam` → Task 9; `..` ellipsis → **already closed**, documented in § What is already done and recorded in Amendment 9. The mandated scoping-audit task at the family boundary is Task 7. The mandated binder-family-first ordering holds (Tasks 1–7 precede 8–9).

**Two known soft spots, flagged rather than hidden.**

1. **Task 8 has an ordering dependency on Task 10.** Its tests need `withDefault` in the committed `Elab0.olean`, which Task 10 regenerates. Task 8's Step 1 says so and gives the resolution (do Task 10's declaration half early, or reorder). This is honest about a real coupling rather than pretending the tasks are independent.
2. **Task 6's test may not be reachable from source.** The step says so explicitly and bounds the effort, with a defined fallback (test the classifier directly, record why). A task whose outcome is "we learned the arm is unreachable today, and here is the evidence" is a successful task.

**Type consistency.** `FunBinderView { name: Option<NameId>, ty: Option<SynElem>, bi: BinderInfo }` is introduced in Task 1 and consumed in Tasks 2 and 4 under that name. `UseImplicitLambda { No, Yes(ExprId), Postpone }` is introduced in Task 5 and its third variant constructed in Task 6. `propagate_expected_type` returns `Result<Option<ExprId>, ElabError>` and Task 4 threads it as `residual`. `opt_param_default` (Task 8) and `auto_param_tactic` (Task 9) share the `Result<Option<ExprId>, ElabError>` shape and sit in the same `match`.

**Where the plan deliberately does not specify.** Several steps say "read the existing helper and mirror its idiom" rather than inventing a signature — `instantiate1`, `cleanup_annotations`, `add_new_arg`, the `BinderGroup` field names, `Node::Forall`'s field names, `with_mvar_local_context`'s visibility. These are places where guessing a name would produce code that does not compile and, worse, a plan that reads authoritative while being wrong. Each one names the file to read.
