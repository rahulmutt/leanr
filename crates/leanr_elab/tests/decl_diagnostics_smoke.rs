//! M4c-1 P2: term-level oracle first lines that the declaration corpus
//! (`oracle_decl.rs`) relies on. Each string was produced by the oracle in
//! the plan-time decl probe (plan `2026-10-03-m4c1-p2-command-elab.md`).

mod support;

use leanr_syntax::builtin;

/// Elaborate `src` against Elab0 with `elab_term_and_synthesize`; the
/// first line of its error, if any.
fn first_line(src: &str) -> Option<String> {
    let r = support::replay_fixture_in("elab", "Elab0.olean");
    support::with_record_elab(
        &r,
        src,
        &builtin::snapshot(),
        |elab, elem, kinds| match elab.elab_term_and_synthesize(elem, kinds, None) {
            Ok(_) => None,
            Err(e) => Some(
                e.oracle_first_line()
                    .unwrap_or_else(|| format!("<no line: {e:?}>")),
            ),
        },
    )
}

#[test]
fn ascription_mismatch_is_type_mismatch() {
    // oracle: `def em : Nat := True.intro` -> "Type mismatch" (ensureHasType, f? = none)
    assert_eq!(
        first_line("(True.intro : Nat)").as_deref(),
        Some("Type mismatch")
    );
}

#[test]
fn argument_mismatch_is_application_type_mismatch() {
    // oracle: `def da : Nat := pick True.intro Nat.zero`
    assert_eq!(
        first_line("pick True.intro Nat.zero").as_deref(),
        Some("Application type mismatch: The argument")
    );
}

#[test]
fn argument_already_in_f_says_the_last() {
    // oracle: `def dl : Nat := dep Nat Nat` — `f = dep Nat`, `a = Nat`,
    // `f.getAppArgs.any (· == a)` holds (Meta/Check.lean:254).
    assert_eq!(
        first_line("dep Nat Nat").as_deref(),
        Some("Application type mismatch: The last")
    );
}

#[test]
fn unknown_identifier_first_line() {
    // oracle: `def uib : Nat := nope` -> "Unknown identifier `nope`"
    assert_eq!(
        first_line("nope").as_deref(),
        Some("Unknown identifier `nope`")
    );
}

/// `∀ (α β : Sort _), α → β → α`: the two binder domains are `Sort ?u`
/// and `Sort ?v` with DISTINCT level mvars (oracle `elabBinderViews`
/// elaborates the group's type once per name, `Binders.lean:208-223`;
/// probe: `def tw (α β : Sort _) …` gets `[u_1, u_2]`).
#[test]
fn binder_group_type_is_elaborated_per_name() {
    use leanr_kernel::bank::terms::Node;
    let r = support::replay_fixture_in("elab", "Elab0.olean");
    support::with_record_elab(
        &r,
        "∀ (α β : Sort _), α → β → α",
        &builtin::snapshot(),
        |elab, elem, kinds| {
            let e = elab
                .elab_term_and_synthesize(elem, kinds, None)
                .expect("elaborates");
            let base = Some(elab.view.store);
            let st = elab.mctx.store();
            let Node::Forall {
                binder_type: t1,
                body,
                ..
            } = st.expr_node(base, e)
            else {
                panic!("outer forall")
            };
            let Node::Forall {
                binder_type: t2, ..
            } = st.expr_node(base, body)
            else {
                panic!("inner forall")
            };
            assert_ne!(
                t1, t2,
                "one shared `Sort ?u` for both binders: the group was elaborated once"
            );
        },
    );
}
