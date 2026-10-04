//! M4c-2b-i command-layer pins (plan Task 3). Expectations are the
//! oracle's (plan § Plan-time oracle facts); the full differential gate
//! is `oracle_file.rs` (Task 5).
mod support;

use leanr_elab::ElabError;

/// (names admitted per command, stop index + first line or seam message)
fn run(src: &str) -> (Vec<Vec<String>>, Option<(usize, String)>) {
    support::with_file_elab(src, |ce, cmds, kinds| {
        let out = ce.elab_commands(cmds, kinds);
        let st = ce.env().store();
        let done = out
            .done
            .iter()
            .map(|ns| {
                ns.iter()
                    .map(|&n| st.to_name(None, Some(n)).to_string())
                    .collect()
            })
            .collect();
        let stopped = out.stopped.map(|(i, e)| {
            (
                i,
                match e {
                    ElabError::UnsupportedSyntax(m) => format!("SEAM {m}"),
                    e => e.oracle_first_line().unwrap_or_else(|| format!("{e:?}")),
                },
            )
        });
        (done, stopped)
    })
}

fn v(xs: &[&[&str]]) -> Vec<Vec<String>> {
    xs.iter()
        .map(|c| c.iter().map(|s| s.to_string()).collect())
        .collect()
}

#[test]
fn namespaces_prefix_declarations_and_end_pops() {
    let (done, stop) =
        run("namespace A.B\ndef f : Nat := Nat.zero\nend B\ndef g : Nat := B.f\nend A");
    assert_eq!(stop, None);
    assert_eq!(done, v(&[&[], &["A.B.f"], &[], &["A.g"], &[]]));
    // A multi-component `end` pops one scope per component (implementer
    // probe: the oracle admits `g` at the root). The plan's mutation 1
    // discriminator: `end B` above has `endSize` 1 either way.
    let (done, stop) = run("namespace A.B\ndef f : Nat := Nat.zero\nend A.B\ndef g : Nat := A.B.f");
    assert_eq!(stop, None);
    assert_eq!(done, v(&[&[], &["A.B.f"], &[], &["g"]]));
}

#[test]
fn dotted_root_and_protected_names() {
    assert_eq!(
        run("namespace A\ndef B.f : Nat := Nat.zero\ndef g : Nat := B.f\nend A").0,
        v(&[&[], &["A.B.f"], &["A.g"], &[]])
    );
    assert_eq!(
        run("namespace A\ndef _root_.rx : Nat := Nat.zero\ndef f : Nat := rx\nend A").0,
        v(&[&[], &["rx"], &["A.f"], &[]])
    );
    assert_eq!(
        run("namespace A\nprotected def p : Nat := Nat.zero\ndef q : Nat := A.p\nend A").0,
        v(&[&[], &["A.p"], &["A.q"], &[]])
    );
    let (_, stop) = run("namespace A\nprotected def p : Nat := Nat.zero\ndef q : Nat := p");
    assert_eq!(stop, Some((2, "Unknown identifier `p`".into())));
}

#[test]
fn open_forms() {
    assert_eq!(
        run("open Scope0\ndef f : Nat := shown\ndef g : Nat := Inner.deep").1,
        None
    );
    assert_eq!(
        run("open Scope0 hiding shown\ndef f : Nat := shown").1,
        Some((1, "Unknown identifier `shown`".into()))
    );
    assert_eq!(
        run("open Scope0 renaming shown → sh\ndef f : Nat := sh").1,
        None
    );
    assert_eq!(
        run("open Scope0 (nope)").1,
        Some((0, "Unknown constant `Scope0.nope`".into()))
    );
    assert_eq!(
        run("open Nope").1,
        Some((0, "unknown namespace `Nope`".into()))
    );
    assert_eq!(
        run("open Scope0 in\ndef f : Nat := shown\ndef g : Nat := Scope0.shown").1,
        None
    );
    assert_eq!(
        run("section\nopen Scope0\nend\ndef f : Nat := shown").1,
        Some((3, "Unknown identifier `shown`".into()))
    );
    assert_eq!(
        run("open Scope0\ndef f : Nat := hidden").1,
        Some((1, "Unknown identifier `hidden`".into()))
    );
    assert_eq!(run("def f : Nat := ex").0, v(&[&["f"]]));
    // Plan mutation 2: a `_root_` name is not expanded into `namespace A`,
    // so only `registerNamePrefixes` makes `A` a namespace.
    assert_eq!(
        run("def _root_.A.k : Nat := Nat.zero\nopen A\ndef f : Nat := k").1,
        None
    );
    // Plan mutation 3: `open A B`'s second namespace sees the first
    // (`Elab/Open.lean:75`, a local copy of the open decls).
    assert_eq!(run("open Scope0 Inner\ndef f : Nat := deep").1, None);
    // Plan mutation 4 (oracle record `err/inScoped`): `open … in def f` is
    // ONE command, and its opens do not leak.
    assert_eq!(
        run("open Scope0 in\ndef f : Nat := shown\ndef g : Nat := shown").1,
        Some((1, "Unknown identifier `shown`".into()))
    );
}

#[test]
fn end_errors_are_the_oracles() {
    for (src, line) in [
        (
            "def f : Nat := Nat.zero\nend",
            "Invalid `end`: There is no current scope to end",
        ),
        (
            "namespace A\nend",
            "Missing name after `end`: Expected the current scope name `A`",
        ),
        (
            "namespace A\nend A.B",
            "Invalid name after `end`: `A.B` contains too many components",
        ),
        (
            "namespace A\nend B",
            "Invalid name after `end`: Expected `A`, but found `B`",
        ),
        (
            "section\nend A",
            "Unexpected name `A` after `end`: The current section is unnamed",
        ),
    ] {
        let (_, stop) = run(src);
        assert_eq!(stop.map(|s| s.1).as_deref(), Some(line), "{src:?}");
    }
}

#[test]
fn declaration_name_errors_are_the_oracles() {
    assert_eq!(
        run("protected def p : Nat := Nat.zero").1,
        Some((0, "protected declarations must be in a namespace".into()))
    );
    assert_eq!(run("def _root_ : Nat := Nat.zero").1, Some((0,
        "invalid declaration name `_root_`, `_root_` is a prefix used to refer to the 'root' namespace".into())));
    assert_eq!(
        run("namespace A\ndef f : Nat := Nat.zero\ndef f : Nat := Nat.zero").1,
        Some((2, "`A.f` has already been declared".into()))
    );
    assert_eq!(
        run("namespace A\ntheorem t : Nat := Nat.zero").1,
        Some((1, "type of theorem `A.t` is not a proposition".into()))
    );
}

/// Review Focus 1.
#[test]
fn an_unclosed_namespace_at_end_of_input_is_fine() {
    assert_eq!(
        run("namespace A\ndef f : Nat := Nat.zero"),
        (v(&[&[], &["A.f"]]), None)
    );
}

/// Review Focus 2 (end to end).
#[test]
fn ambiguous_identifiers_seam_end_to_end() {
    for src in [
        "def shown : Nat := Nat.zero\nopen Scope0\ndef f : Nat := shown",
        "def Scope0.ex : Nat := Nat.zero\nopen Scope0\ndef f : Nat := ex",
        "namespace A\ndef k : Nat := Nat.zero\nend A\nnamespace B\ndef k : Nat := Nat.zero\nend B\nopen A B\ndef f : Nat := k",
    ] {
        let (_, stop) = run(src);
        let m = stop.expect("stops").1;
        assert!(m.starts_with("SEAM ") && m.ends_with(" — M4c-2b-ii"), "{src:?}: {m}");
    }
}

/// Review Focus 4.
#[test]
fn reserved_and_shadowing_names_seam() {
    for (src, needle) in [
        ("def enumToBitVec : Nat := Nat.zero", "reserved name"),
        (
            "def f : Nat := Nat.zero\ndef f.eq_1 : Nat := Nat.zero",
            "reserved name",
        ),
        (
            "def f : Nat := Nat.zero\ndef f.fun_cases : Nat := Nat.zero",
            "reserved name",
        ),
        ("def Prod.fst : Nat := Nat.zero", "structure field"),
    ] {
        let m = run(src).1.expect("stops").1;
        assert!(
            m.starts_with("SEAM ") && m.contains(needle) && m.ends_with(" — later M4"),
            "{src:?}: {m}"
        );
    }
    // Not reserved: the parent is an axiom / undeclared (oracle admits both).
    assert_eq!(run("axiom f : Nat\ndef f.eq_1 : Nat := Nat.zero").1, None);
}

/// Review Focus 5.
#[test]
fn deferred_scope_forms_are_named_seams() {
    for (src, needle) in [
        ("open scoped Scope0", "`open scoped`"),
        ("noncomputable section", "section modifier"),
        (
            "def f : Nat := open Scope0 in shown",
            "Lean.Parser.Term.open",
        ),
    ] {
        let m = run(src).1.expect("stops").1;
        assert!(
            m.starts_with("SEAM ") && m.contains(needle) && m.ends_with(" — later M4"),
            "{src:?}: {m}"
        );
    }
}

/// Implementer-probed against the pinned oracle (`lean` v4.33.0-rc1,
/// 2026-10-04): first error line per source.
#[test]
fn oracle_probed_edge_cases() {
    for (src, at, line) in [
        // `ensureValidNamespace` names the prefix up to the LAST `_root_`.
        (
            "def _root_.A._root_.B._root_.f : Nat := Nat.zero",
            0,
            "invalid namespace `A._root_.B._root_`, `_root_` is a reserved namespace",
        ),
        // `setDeclIdName`: the message prints the expanded short name.
        (
            "def A.eh : _ := fun x => x",
            0,
            "Failed to infer type of definition `eh`",
        ),
        (
            "def A.«x.y» : _ := fun x => x",
            0,
            "Failed to infer type of definition `«x.y»`",
        ),
        // `resolveId` in every `open` form.
        (
            "open Scope0 renaming nope → y",
            0,
            "Unknown constant `Scope0.nope`",
        ),
        (
            "open Scope0 hiding nope",
            0,
            "Unknown constant `Scope0.nope`",
        ),
        // `expandInCmd`'s closing bare `end`.
        (
            "open Scope0 in\nnamespace Q",
            0,
            "Missing name after `end`: Expected the current scope name `Q`",
        ),
        (
            "namespace A.B\nsection C\nend B",
            2,
            "Invalid name after `end`: Expected `C`, but found `B`",
        ),
    ] {
        assert_eq!(run(src).1, Some((at, line.to_string())), "{src:?}");
    }
}

/// Review Focus 3. Oracle: each is "fail to show termination for".
#[test]
fn recursive_references_seam_in_namespaces() {
    for src in [
        "def x : Nat := Nat.zero\nnamespace A\ndef x : Nat := x",
        "theorem tt : True := True.intro\nnamespace A\ntheorem tt : True := tt",
        "def x : Nat := Nat.zero\ndef A.x : Nat := x",
        "namespace A\ndef f : Nat := A.f",
        "def x : Nat := Nat.zero\nnamespace A\nopaque x : Nat := x",
        "def x : Nat := Nat.zero\nnamespace A\nabbrev x : Nat := x",
        "example : Nat := _example",
        "def sr : Nat := sr.foo",
        "def sr : Nat := sr",
        "def sr : Nat := «sr»",
        "def «sr» : Nat := sr",
        "def B.f : Nat := Nat.zero\nnamespace A\ndef B.f : Nat := B.f",
    ] {
        let m = run(src).1.expect("stops").1;
        assert!(
            m.contains("recursive reference") && m.ends_with(" — later M4 (recursion)"),
            "{src:?}: {m}"
        );
    }
}

/// `globalDeclFound` (`ResolveName.lean:580-622`): a global `foo.aux`
/// beats the aux local `foo` with a field; axioms have no aux local; a
/// binder shadows the aux local; the header has no aux local.
#[test]
fn non_recursive_self_like_references_elaborate() {
    assert_eq!(
        run("def foo.aux : Nat := Nat.zero\ndef foo : Nat := foo.aux").0,
        v(&[&["foo.aux"], &["foo"]])
    );
    assert_eq!(
        run("def x : Nat := Nat.zero\nnamespace A\naxiom x : Nat").1,
        None
    );
    assert_eq!(run("def g (g : Nat) : Nat := g").1, None);
    assert_eq!(
        run("def x : Nat := Nat.zero\nnamespace A\ndef x : Eq x x := rfl").0,
        v(&[&["x"], &[], &["A.x"]])
    );
    assert_eq!(run("def sr : Nat := Nat.zero\ndef srx : Nat := sr").1, None);
}
