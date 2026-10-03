//! M4c-1 P2 declaration differential gate (spec
//! `docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md`
//! § Harness). Every committed `{id, src, consts|err}` record of
//! `decl-queries.jsonl` (`tests/fixtures/elab/dump_decls.lean`) is parsed
//! by leanr's own parser as exactly one command.

mod support;

/// `wc -l tests/fixtures/elab/decl-queries.jsonl` at the last deliberate
/// regen. `>=`: adding a record is a one-line bump, not a failing gate.
const CORPUS_FLOOR: usize = 79;

#[test]
fn decl_corpus_sources_parse_as_one_command() {
    let text = std::fs::read_to_string(support::fixture_in("elab", "decl-queries.jsonl"))
        .expect("committed decl corpus");
    let mut n = 0;
    for line in text.lines().filter(|l| !l.trim().is_empty()) {
        let q: serde_json::Value = serde_json::from_str(line).expect("valid JSONL");
        let src = q["src"].as_str().expect("src field");
        let _ = support::parse_command(src);
        n += 1;
    }
    assert!(
        n >= CORPUS_FLOOR,
        "decl corpus shrank: {n} < {CORPUS_FLOOR}"
    );
}

#[test]
fn oracle_decl_gate() {
    let checked = support::run_decl_corpus("decl-queries.jsonl", |_| true);
    assert!(
        checked >= CORPUS_FLOOR,
        "decl corpus shrank: checked {checked}, floor {CORPUS_FLOOR}. Check \
         `dump_decls.lean`'s stderr for a dropped record, or lower the floor deliberately."
    );
}

fn decl_result(src: &str) -> Result<Vec<String>, leanr_elab::ElabError> {
    support::with_command_elab(src, |ce, cmd, kinds| {
        ce.elab_decl(cmd, kinds).map(|ns| {
            ns.iter()
                .map(|&n| support::name_to_string(ce.env().store(), None, Some(n)))
                .collect()
        })
    })
}

fn seam_message(src: &str) -> String {
    match decl_result(src) {
        Err(leanr_elab::ElabError::UnsupportedSyntax(m)) => m,
        other => panic!("{src:?}: expected a named seam, got {other:?}"),
    }
}

#[test]
fn header_unknown_ident_is_the_auto_bound_seam() {
    // The oracle auto-binds `α` (probe: `def ab (a : α) : α := a` admits `ab.{u_1}`).
    let m = seam_message("def ab (a : α) : α := a");
    assert!(m.contains("auto-bound") && m.contains("M4c-2"), "{m}");
}

#[test]
fn header_unknown_universe_is_the_auto_bound_seam() {
    // probe: `def uuh (α : Sort w) : Sort w := α` admits `uuh.{w}`.
    let m = seam_message("def uuh (α : Sort w) : Sort w := α");
    assert!(m.contains("auto-bound"), "{m}");
}

#[test]
fn let_and_have_in_a_value_are_the_let_to_have_seam() {
    assert!(seam_message("def sl : Nat := let x := Nat.zero; x").contains("letToHave"));
    assert!(seam_message("def sh : Nat := have x := Nat.zero; x").contains("letToHave"));
}

#[test]
fn example_is_checked_but_not_added() {
    support::with_command_elab("example : Nat := Nat.zero", |ce, cmd, kinds| {
        let before = ce.env().len();
        assert_eq!(
            ce.elab_decl(cmd, kinds).expect("elaborates"),
            Vec::<leanr_kernel::bank::NameId>::new()
        );
        assert_eq!(ce.env().len(), before, "an example must not add constants");
    });
}

#[test]
fn level_mvar_without_error_info_hits_the_fallback() {
    // No binder registers a level error info here: the level mvar comes from
    // the constant `PUnit.unit.{?w}` (Prod's `v` := ?w). Oracle probe (a
    // scratch copy of `dump_decls.lean`, v4.33.0-rc1): `ensureNoUnassigned
    // LevelMVarsAtPreDef`'s fallback (`PreDefinition/Main.lean:84-93`).
    // Pins Task 6 mutation 7, which `err/levelMVarValue` (a binder-info hit)
    // does not kill.
    match decl_result("def lv2 : Nat := Prod.fst (Prod.mk Nat.zero PUnit.unit)") {
        Err(e) => assert_eq!(
            e.oracle_first_line().as_deref(),
            Some("declaration `lv2` contains universe level metavariables at the expression"),
            "{e:?}"
        ),
        Ok(ns) => panic!("a value with an unassigned level mvar was admitted: {ns:?}"),
    }
}

#[test]
fn axiom_header_unknown_ident_is_the_auto_bound_seam() {
    // `elabAxiom` also runs under `withAutoBoundImplicit` (`Declaration.lean:109`).
    let m = seam_message("axiom aa (a : α) : α");
    assert!(m.contains("auto-bound"), "{m}");
}

/// The admitted main declaration's `NameId` for `src` (the last name).
fn with_main_const<R>(
    src: &str,
    k: impl FnOnce(&leanr_kernel::Environment, leanr_kernel::bank::NameId) -> R,
) -> R {
    support::with_command_elab(src, |ce, cmd, kinds| {
        let ns = ce
            .elab_decl(cmd, kinds)
            .unwrap_or_else(|e| panic!("{src:?}: {e:?}"));
        let main = *ns.last().expect("a main declaration");
        k(ce.env(), main)
    })
}

#[test]
fn quoted_decl_name_is_decoded() {
    // Oracle probe (scratch copy of `dump_decls.lean`, v4.33.0-rc1):
    // `def «gq» : Nat := Nat.zero` admits `gq`.
    assert_eq!(
        decl_result("def «gq» : Nat := Nat.zero").expect("admits"),
        vec!["gq".to_string()]
    );
}

#[test]
fn quoted_dotted_decl_name_is_one_atomic_component() {
    // Oracle probe: `def «a.b» : Nat := Nat.zero` admits the ATOMIC `«a.b»`
    // at the root (no namespace is opened).
    with_main_const("def «a.b» : Nat := Nat.zero", |env, n| {
        let name = env.store().to_name(None, Some(n));
        assert_eq!(name.to_string(), "a.b");
        assert!(
            matches!(
                &*name,
                leanr_kernel::Name::Str { parent, part }
                    if part == "a.b" && matches!(**parent, leanr_kernel::Name::Anonymous)
            ),
            "`«a.b»` must be one component, got {name:?}"
        );
    });
}

#[test]
fn quoted_universe_name_is_decoded() {
    // Oracle probe: `def gu2.{«u»} (α : Sort «u») (a : α) : α := a` has
    // level params `[u]`.
    with_main_const(
        "def gu2.{«u»} (α : Sort «u») (a : α) : α := a",
        |env, n| {
            let ci = env.get(n).expect("admitted");
            let lps: Vec<String> = ci
                .constant_val()
                .level_params
                .iter()
                .map(|&l| support::name_to_string(env.store(), None, Some(l)))
                .collect();
            assert_eq!(lps, vec!["u".to_string()]);
        },
    );
}

/// The binder names of `e`'s leading `∀` telescope.
fn pi_binder_names(
    env: &leanr_kernel::Environment,
    mut e: leanr_kernel::bank::ExprId,
) -> Vec<String> {
    use leanr_kernel::bank::terms::Node;
    let mut out = Vec::new();
    while let Node::Forall {
        binder_name, body, ..
    } = env.store().expr_node(None, e)
    {
        out.push(support::name_to_string(env.store(), None, binder_name));
        e = body;
    }
    out
}

#[test]
fn quoted_binder_name_is_decoded() {
    // Oracle probes: `def fb («x» : Nat) : Nat := x` and `… := «x»` both
    // admit with binder name `x`; `fh («x.y» : Nat)` admits with the ATOMIC
    // binder name `«x.y»`. The gate erases binder names, so pin them here.
    for src in [
        "def fb («x» : Nat) : Nat := x",
        "def fb2 («x» : Nat) : Nat := «x»",
    ] {
        with_main_const(src, |env, n| {
            let ty = env.get(n).expect("admitted").constant_val().ty;
            assert_eq!(pi_binder_names(env, ty), vec!["x".to_string()], "{src}");
        });
    }
    with_main_const("def fh («x.y» : Nat) : Nat := Nat.zero", |env, n| {
        let ty = env.get(n).expect("admitted").constant_val().ty;
        assert_eq!(pi_binder_names(env, ty), vec!["x.y".to_string()]);
    });
}

#[test]
fn dotted_binder_name_is_rejected() {
    // Oracle probes: `ensureAtomicBinderName` (`Elab/Binders.lean:188-191`)
    // in both `elabBinderViews` and `elabFunBinderViews`.
    for (src, n) in [
        ("def f18 (a.b : Nat) : Nat := Nat.zero", "a.b"),
        ("def fg (x.«y» : Nat) : Nat := Nat.zero", "x.y"),
        ("def fe (_root_.x : Nat) : Nat := Nat.zero", "_root_.x"),
        ("def fc := fun (a.b : Nat) => Nat.zero", "a.b"),
        ("def fc2 := fun (a.b : Nat) => a.b", "a.b"),
        ("def fc3 := fun a.b => Nat.zero", "a.b"),
    ] {
        match decl_result(src) {
            Err(e) => assert_eq!(
                e.oracle_first_line(),
                Some(format!("invalid binder name `{n}`, it must be atomic")),
                "{src}: {e:?}"
            ),
            Ok(ns) => panic!("{src:?}: a dotted binder name was admitted: {ns:?}"),
        }
    }
}

#[test]
fn root_prefixed_atomic_name_is_admitted() {
    // Oracle probe: `def _root_x : Nat := Nat.zero` admits `_root_x`; only
    // `_root_` itself or a `_root_.` prefix opens the root namespace.
    assert_eq!(
        decl_result("def _root_x : Nat := Nat.zero").expect("admits"),
        vec!["_root_x".to_string()]
    );
}

#[test]
fn quoted_self_reference_is_a_recursion_seam() {
    // Oracle probe: `def sr : Nat := «sr»` is recursion ("fail to show
    // termination for sr").
    let m = seam_message("def sr : Nat := «sr»");
    assert!(m.contains("recursive reference to `sr`"), "{m}");
}

#[test]
fn aux_lemma_reuse_across_declarations_is_a_seam() {
    // Oracle probe (env threaded across commands): after `na` admits
    // `na._proof_1`, an identical `nb` REUSES it (`auxLemmasExt`,
    // `Meta/Tactic/AuxLemma.lean:70-73`) and admits only `nb`.
    let na = "def na (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl";
    let nb = "def nb (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl";
    support::with_command_elab(na, |ce, cmd, kinds| {
        let first = ce.elab_decl(cmd, kinds).expect("na admits");
        assert_eq!(first.len(), 2, "na._proof_1 then na");
        let before = ce.env().len();
        let (parsed, cmd2) = support::parse_command(nb);
        match ce.elab_decl(&cmd2, &parsed.tree.kinds) {
            Err(leanr_elab::ElabError::UnsupportedSyntax(m)) => {
                assert!(m.contains("auxLemmasExt") && m.contains("M4c-2"), "{m}")
            }
            other => panic!("nb: expected the aux-reuse seam, got {other:?}"),
        }
        assert_eq!(ce.env().len(), before, "the seam must add nothing");
        // A later declaration that mints no aux lemma is unaffected.
        let (parsed, cmd3) = support::parse_command("def nz : Nat := Nat.zero");
        assert_eq!(
            ce.elab_decl(&cmd3, &parsed.tree.kinds).expect("nz").len(),
            1
        );
    });
}
