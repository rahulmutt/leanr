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

/// Elaborate `src` (no synthesis failure expected), then report the first
/// unassigned-mvar error the oracle's `logUnassignedUsingErrorInfos` would
/// log for the mvars left in the result; and the level-mvar one.
fn unassigned_first_lines(src: &str) -> (Option<String>, Option<String>) {
    let r = support::replay_fixture_in("elab", "Elab0.olean");
    support::with_record_elab(&r, src, &builtin::snapshot(), |elab, elem, kinds| {
        let e = elab.elab_term(elem, kinds, None).expect("elaborates");
        elab.synthesize_synthetic_mvars_no_postponing(kinds)
            .expect("synthesizes");
        let e = elab.mctx.instantiate_mvars(e).expect("instantiates");
        let pending = elab.get_mvars(e).expect("get_mvars");
        let expr_line = elab
            .log_unassigned_using_error_infos(&pending)
            .expect("log")
            .and_then(|err| err.oracle_first_line());
        let lpending = elab.get_level_mvars(e).expect("get_level_mvars");
        let level_line = elab
            .log_unassigned_level_mvars_using_error_infos(&lpending)
            .expect("log levels")
            .and_then(|err| err.oracle_first_line());
        (expr_line, level_line)
    })
}

#[test]
fn hole_argument_names_its_parameter() {
    // oracle: `def eh2 : Nat := pick _ Nat.zero`
    assert_eq!(
        unassigned_first_lines("pick _ Nat.zero").0.as_deref(),
        Some("don't know how to synthesize placeholder for argument `x`")
    );
}

#[test]
fn most_recent_error_info_is_reported_first() {
    // `mvarErrorInfos` is consed: the hole for `y` (registered last) is logged first.
    assert_eq!(
        unassigned_first_lines("pick _ _").0.as_deref(),
        Some("don't know how to synthesize placeholder for argument `y`")
    );
}

#[test]
fn bare_hole_has_no_argument_name() {
    // oracle: `def eh3 := _`
    assert_eq!(
        unassigned_first_lines("_").0.as_deref(),
        Some("don't know how to synthesize placeholder")
    );
}

#[test]
fn implicit_argument_names_its_parameter() {
    // oracle: `def eu := id`
    assert_eq!(
        unassigned_first_lines("id").0.as_deref(),
        Some("don't know how to synthesize implicit argument `α`")
    );
}

#[test]
fn untyped_fun_binder_is_failed_to_infer() {
    // oracle: `def eh4 := fun x => x`
    assert_eq!(
        unassigned_first_lines("fun x => x").0.as_deref(),
        Some("Failed to infer type of binder `x`")
    );
}

#[test]
fn forall_binder_hole_is_failed_to_infer() {
    // oracle (decl header analogue): `def eh (x : _) : Nat := Nat.zero`
    assert_eq!(
        unassigned_first_lines("∀ (x : _), Nat").0.as_deref(),
        Some("Failed to infer type of binder `x`")
    );
}

#[test]
fn level_mvar_in_hole_binder_names_the_binder_type() {
    // oracle: `def lv : Nat := (fun (_ : Sort _) => Nat.zero) PUnit`
    assert_eq!(
        unassigned_first_lines("(fun (_ : Sort _) => Nat.zero) PUnit")
            .1
            .as_deref(),
        Some("Failed to infer universe levels in binder type")
    );
}
