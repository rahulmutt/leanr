//! `DefView`: the M4c-1 subset of oracle `mkDefView` (`Elab/DefView.lean:
//! 140-230`) plus `elabAxiom`'s syntax access (`Elab/Declaration.lean:
//! 101-105`). Decodes one `declaration` command and raises a named seam for
//! everything outside M4c-1 (spec § Architecture, `DefView::from_syntax`).

use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::{NodeOrToken, SyntaxNode};

use crate::app::head::ident_components;
use crate::dispatch::{non_trivia_children, SynElem};
use crate::error::ElabError;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DefKind {
    Def,
    Theorem,
    Abbrev,
    Opaque,
    Example,
    Axiom,
}

pub(crate) struct DefView {
    pub kind: DefKind,
    /// The declaration name's components as written, decoded (`«»`
    /// stripped, so `«a.b»` is ONE component `a.b`); a leading `_root_` is
    /// kept. `None` for `example`, whose name is `_example`
    /// (`DefView.lean:201-208`). `CommandElab` replaces a dotted name by
    /// its last component once [`expand_decl_namespace`] has opened the
    /// namespace.
    pub name: Option<Vec<String>>,
    /// The `protected` modifier (`declModifiers` slot 3).
    pub protected: bool,
    /// The `declId` node (for messages); `None` for `example`.
    pub decl_id: Option<SynElem>,
    /// `.{u, v}` names in source order.
    pub univ_names: Vec<String>,
    /// The bracketed binder groups, in order.
    pub binders: Vec<SyntaxNode>,
    /// The `: T` term, if written (always `Some` for theorem/opaque/axiom).
    pub ty: Option<SynElem>,
    /// The `:= v` term (`None` only for `axiom`).
    pub value: Option<SynElem>,
}

fn seam(what: impl Into<String>) -> ElabError {
    ElabError::UnsupportedSyntax(what.into())
}

fn ill(what: &str) -> ElabError {
    ElabError::IllFormedSyntax(format!("declaration: {what}"))
}

fn as_node(el: Option<&SynElem>, what: &str) -> Result<SyntaxNode, ElabError> {
    match el {
        Some(NodeOrToken::Node(n)) => Ok(n.clone()),
        _ => Err(ill(what)),
    }
}

fn is_empty(n: &SyntaxNode) -> bool {
    non_trivia_children(n).is_empty()
}

impl DefView {
    pub(crate) fn from_syntax(
        cmd: &SyntaxNode,
        kinds: &KindInterner,
    ) -> Result<DefView, ElabError> {
        let ck = kinds.name(cmd.kind());
        if ck != "Lean.Parser.Command.declaration" {
            return Err(super::command_seam(ck));
        }
        let ch = non_trivia_children(cmd);
        let mods = as_node(ch.first(), "declModifiers")?;
        let protected = check_modifiers(&mods)?;
        let decl = as_node(ch.get(1), "declaration kind")?;
        let dk = kinds.name(decl.kind());
        let d = non_trivia_children(&decl);
        // (kind, declId, declSig, optDeclSig, declVal) — owned, so `opaque`
        // can hand over the declValSimple INSIDE its optional slot.
        type Parts = (
            DefKind,
            Option<SynElem>,
            Option<SynElem>,
            Option<SynElem>,
            Option<SynElem>,
        );
        let (kind, decl_id, sig, opt_sig, val): Parts = match dk {
            "Lean.Parser.Command.definition" => {
                if let Some(NodeOrToken::Node(der)) = d.get(4) {
                    if !is_empty(der) {
                        return Err(seam("deriving — later M4"));
                    }
                }
                (
                    DefKind::Def,
                    d.get(1).cloned(),
                    None,
                    d.get(2).cloned(),
                    d.get(3).cloned(),
                )
            }
            "Lean.Parser.Command.theorem" => (
                DefKind::Theorem,
                d.get(1).cloned(),
                d.get(2).cloned(),
                None,
                d.get(3).cloned(),
            ),
            "Lean.Parser.Command.abbrev" => (
                DefKind::Abbrev,
                d.get(1).cloned(),
                None,
                d.get(2).cloned(),
                d.get(3).cloned(),
            ),
            "Lean.Parser.Command.opaque" => {
                let slot = as_node(d.get(3), "opaque value slot")?;
                let Some(dv) = non_trivia_children(&slot).first().cloned() else {
                    return Err(seam(
                        "`opaque` without a value — later M4 (Inhabited/Nonempty default)",
                    ));
                };
                (
                    DefKind::Opaque,
                    d.get(1).cloned(),
                    d.get(2).cloned(),
                    None,
                    Some(dv),
                )
            }
            "Lean.Parser.Command.axiom" => (
                DefKind::Axiom,
                d.get(1).cloned(),
                d.get(2).cloned(),
                None,
                None,
            ),
            "Lean.Parser.Command.example" => (
                DefKind::Example,
                None,
                None,
                d.get(1).cloned(),
                d.get(2).cloned(),
            ),
            other => return Err(seam(format!("declaration kind `{other}` — later M4"))),
        };
        let (name, univ_names) = match &decl_id {
            Some(id) => decode_decl_id(&as_node(Some(id), "declId")?, kinds)?,
            None => (None, Vec::new()),
        };
        let (binders, ty) = match (&sig, &opt_sig) {
            (Some(s), _) => decode_sig(&as_node(Some(s), "declSig")?, kinds, false)?,
            (None, Some(s)) => decode_sig(&as_node(Some(s), "optDeclSig")?, kinds, true)?,
            (None, None) => return Err(ill("missing signature")),
        };
        let value = match &val {
            None => None,
            Some(v) => Some(decode_decl_val(&as_node(Some(v), "declVal")?, kinds)?),
        };
        // The short name after `expand_decl_namespace`: the last component.
        if let (Some(n), Some(v)) = (name.as_ref().and_then(|n| n.last()), &value) {
            check_no_self_reference(n, v, kinds)?;
        }
        Ok(DefView {
            kind,
            name,
            protected,
            decl_id,
            univ_names,
            binders,
            ty,
            value,
        })
    }
}

/// declModifiers' 7 slots (`Command.lean:114-121`). Only `protected`
/// (slot 3) is accepted; returns whether it is present.
fn check_modifiers(mods: &SyntaxNode) -> Result<bool, ElabError> {
    const PROTECTED: usize = 3;
    const SEAMS: [&str; 7] = [
        "doc comment — later M4 (docs)",
        "attributes — later M4",
        "visibility modifier — later M4",
        "",
        "`meta`/`noncomputable` — later M4 (compilation)",
        "`unsafe` — later M4",
        "`partial`/`nonrec` — later M4 (recursion)",
    ];
    let mut protected = false;
    for (i, slot) in non_trivia_children(mods).iter().enumerate() {
        let empty = matches!(slot, NodeOrToken::Node(n) if is_empty(n));
        if empty {
            continue;
        }
        if i == PROTECTED {
            protected = true;
        } else {
            return Err(seam(
                *SEAMS.get(i).unwrap_or(&"declaration modifier — later M4"),
            ));
        }
    }
    Ok(protected)
}

/// oracle: `expandDeclNamespace?` (`Elab/Declaration.lean:90-99`) with
/// `ensureValidNamespace` (`:18-25`): `def A.B.f` → `(["A","B"], "f")`;
/// atomic, `_root_`-prefixed and nameless (`example`) → `None`. A
/// `_root_`-prefixed name's remaining components are checked: the LAST
/// `_root_` among them is the error (`ensureValidNamespace` checks the
/// last component first, then recurses on the prefix), and the error
/// names the prefix ending there.
pub(crate) fn expand_decl_namespace(
    view: &DefView,
) -> Result<Option<(Vec<String>, String)>, ElabError> {
    let Some(comps) = &view.name else {
        return Ok(None);
    };
    match comps.as_slice() {
        [root, rest @ ..] if root == "_root_" => {
            if let Some(i) = rest.iter().rposition(|c| c == "_root_") {
                return Err(ElabError::InvalidNamespace(rest[..=i].join(".")));
            }
            Ok(None)
        }
        [] | [_] => Ok(None),
        [ns @ .., short] => Ok(Some((ns.to_vec(), short.clone()))),
    }
}

/// `declId := ident >> optional (".{" >> sepBy1 (ident <|> hole) ", " >> "}")`.
fn decode_decl_id(
    id: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<(Option<Vec<String>>, Vec<String>), ElabError> {
    let ch = non_trivia_children(id);
    let raw = match ch.first() {
        Some(NodeOrToken::Token(t)) if kinds.name(t.kind()) == "<ident>" => t.text().to_string(),
        _ => return Err(ill("declId name")),
    };
    // `id.getId`: the decoded `Name`, `«»` escapes stripped (`«gq»` is
    // `gq`, `«a.b»` the ATOMIC `a.b`). Dotted and `_root_` names are
    // `expand_decl_namespace`'s and `mkDeclName`'s (`header.rs`).
    let name = ident_components(&raw)?;
    let mut univs = Vec::new();
    if let Some(NodeOrToken::Node(opt)) = ch.get(1) {
        for el in non_trivia_children(opt) {
            if let NodeOrToken::Node(list) = el {
                for u in non_trivia_children(&list) {
                    match &u {
                        NodeOrToken::Token(t) if kinds.name(t.kind()) == "<ident>" => {
                            match ident_components(t.text())?.as_slice() {
                                [one] => univs.push(one.clone()),
                                _ => {
                                    return Err(seam(format!(
                                        "dotted universe name `{}` — later M4",
                                        t.text()
                                    )))
                                }
                            }
                        }
                        NodeOrToken::Token(t) if t.text() == "," => {}
                        _ => return Err(seam("universe hole in .{…} — later M4")),
                    }
                }
            }
        }
    }
    Ok((Some(name), univs))
}

/// `declSig := many binder >> typeSpec`; `optDeclSig := many binder >> optType`.
fn decode_sig(
    sig: &SyntaxNode,
    kinds: &KindInterner,
    optional_type: bool,
) -> Result<(Vec<SyntaxNode>, Option<SynElem>), ElabError> {
    let ch = non_trivia_children(sig);
    let bs = as_node(ch.first(), "binders")?;
    let mut binders = Vec::new();
    for b in non_trivia_children(&bs) {
        match b {
            NodeOrToken::Node(n) if kinds.name(n.kind()) != "Lean.Parser.Term.hole" => {
                binders.push(n)
            }
            _ => return Err(seam("bare binder identifier — later M4")),
        }
    }
    let ty_spec = if optional_type {
        let opt = as_node(ch.get(1), "optType")?;
        non_trivia_children(&opt).first().cloned()
    } else {
        ch.get(1).cloned()
    };
    let ty = match ty_spec {
        None => None,
        Some(spec) => {
            let spec = as_node(Some(&spec), "typeSpec")?;
            Some(
                non_trivia_children(&spec)
                    .get(1)
                    .cloned()
                    .ok_or_else(|| ill("typeSpec term"))?,
            )
        }
    };
    Ok((binders, ty))
}

/// `declVal := declValSimple <|> declValEqns <|> whereStructInst`.
fn decode_decl_val(v: &SyntaxNode, kinds: &KindInterner) -> Result<SynElem, ElabError> {
    match kinds.name(v.kind()) {
        "Lean.Parser.Command.declValSimple" => {
            let ch = non_trivia_children(v);
            if let Some(NodeOrToken::Node(suffix)) = ch.get(2) {
                if non_trivia_children(suffix)
                    .iter()
                    .any(|s| matches!(s, NodeOrToken::Node(n) if !is_empty(n)))
                {
                    return Err(seam("termination hints — later M4 (recursion)"));
                }
            }
            if let Some(NodeOrToken::Node(w)) = ch.get(3) {
                if !is_empty(w) {
                    return Err(seam("`where` declarations — later M4"));
                }
            }
            ch.get(1).cloned().ok_or_else(|| ill("declValSimple term"))
        }
        "Lean.Parser.Command.declValEqns" => Err(seam(
            "pattern-matching equations — later M4 (match / equation compiler)",
        )),
        "Lean.Parser.Command.whereStructInst" => Err(seam("`where` structure instance — later M4")),
        other => Err(ill(&format!("declVal kind {other}"))),
    }
}

/// The oracle elaborates the body under `withFunLocalDecls`
/// (`MutualDef.lean:1343`): the short name resolves to the function being
/// defined, i.e. recursion. leanr has no recursion, so any use seams. The
/// scan is conservative: a shadowing binder also seams (never a wrong `Ok`).
fn check_no_self_reference(
    name: &str,
    value: &SynElem,
    kinds: &KindInterner,
) -> Result<(), ElabError> {
    // `name` is decoded; compare each identifier's DECODED first component,
    // so `«sr»` and `«sr».foo` hit as `sr` and `sr.foo` do. The tree also
    // holds zero-width `<ident>` tokens (e.g. inside `fun (_ : T)`), which
    // name nothing.
    let is_hit = |t: &leanr_syntax::tree::SyntaxToken| -> Result<bool, ElabError> {
        Ok(kinds.name(t.kind()) == "<ident>"
            && !t.text().is_empty()
            && ident_components(t.text())?.first().map(String::as_str) == Some(name))
    };
    let mut found = false;
    match value {
        NodeOrToken::Token(t) => found = is_hit(t)?,
        NodeOrToken::Node(n) => {
            for t in n.descendants_with_tokens().filter_map(|el| el.into_token()) {
                if is_hit(&t)? {
                    found = true;
                    break;
                }
            }
        }
    }
    if found {
        return Err(seam(format!(
            "recursive reference to `{name}` — later M4 (recursion)"
        )));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn view_of(src: &str) -> Result<DefView, ElabError> {
        let parsed = leanr_syntax::parse_module(src, &leanr_syntax::builtin::snapshot());
        assert!(parsed.errors.is_empty(), "{src:?}: {:?}", parsed.errors);
        let root = parsed.tree.root();
        let cmd = root
            .children()
            .find(|n| {
                let k = parsed.tree.kinds.name(n.kind());
                k != "Lean.Parser.Module.header" && k != "Lean.Parser.Command.eoi"
            })
            .expect("one command");
        DefView::from_syntax(&cmd, &parsed.tree.kinds)
    }

    fn seam(src: &str) -> String {
        match view_of(src) {
            Err(ElabError::UnsupportedSyntax(m)) => m,
            Err(e) => panic!("{src:?}: expected a named seam, got {e:?}"),
            Ok(_) => panic!("{src:?}: expected a named seam, got a view"),
        }
    }

    #[test]
    fn decodes_a_def_with_universes_binders_type_and_value() {
        let v = view_of("def ue1.{u, v} (α : Sort u) {a : α} : α := a").unwrap();
        assert_eq!(v.kind, DefKind::Def);
        assert_eq!(v.name, Some(vec!["ue1".to_string()]));
        assert_eq!(v.univ_names, vec!["u".to_string(), "v".to_string()]);
        assert_eq!(v.binders.len(), 2);
        assert!(v.ty.is_some() && v.value.is_some());
    }

    #[test]
    fn decodes_every_kind() {
        assert_eq!(
            view_of("theorem t : True := True.intro").unwrap().kind,
            DefKind::Theorem
        );
        assert_eq!(
            view_of("abbrev a := Nat.zero").unwrap().kind,
            DefKind::Abbrev
        );
        assert_eq!(
            view_of("opaque o : Nat := Nat.zero").unwrap().kind,
            DefKind::Opaque
        );
        let ax = view_of("axiom ax (x : Nat) : Nat").unwrap();
        assert_eq!(
            (ax.kind, ax.binders.len(), ax.value.is_none()),
            (DefKind::Axiom, 1, true)
        );
        let ex = view_of("example : Nat := Nat.zero").unwrap();
        assert_eq!((ex.kind, ex.name.is_none()), (DefKind::Example, true));
        let inf = view_of("def inf1 := Nat.zero").unwrap();
        assert!(inf.ty.is_none());
    }

    #[test]
    fn modifiers_are_named_seams() {
        assert!(seam("/-- d -/ def a : Nat := Nat.zero").contains("doc comment"));
        assert!(seam("@[simp] def a : Nat := Nat.zero").contains("attributes"));
        assert!(seam("private def a : Nat := Nat.zero").contains("visibility modifier"));
        assert!(
            view_of("protected def a : Nat := Nat.zero")
                .unwrap()
                .protected
        );
        assert!(!view_of("def a : Nat := Nat.zero").unwrap().protected);
        assert!(seam("noncomputable def a : Nat := Nat.zero").contains("`meta`/`noncomputable`"));
        assert!(seam("unsafe def a : Nat := Nat.zero").contains("`unsafe`"));
        assert!(seam("partial def a : Nat := Nat.zero").contains("`partial`/`nonrec`"));
    }

    fn name_of(src: &str) -> Option<Vec<String>> {
        view_of(src).unwrap().name
    }

    fn comps(xs: &[&str]) -> Option<Vec<String>> {
        Some(xs.iter().map(|s| s.to_string()).collect())
    }

    fn expanded(src: &str) -> Result<Option<(Vec<String>, String)>, ElabError> {
        expand_decl_namespace(&view_of(src).unwrap())
    }

    #[test]
    fn dotted_decl_names_decode_by_component() {
        assert_eq!(
            name_of("def Foo.bar : Nat := Nat.zero"),
            comps(&["Foo", "bar"])
        );
        assert_eq!(
            name_of("def _root_.baz : Nat := Nat.zero"),
            comps(&["_root_", "baz"])
        );
    }

    #[test]
    fn expand_decl_namespace_splits_off_the_short_name() {
        assert_eq!(
            expanded("def A.B.f : Nat := Nat.zero").unwrap(),
            Some((vec!["A".to_string(), "B".to_string()], "f".to_string()))
        );
        for src in [
            "def f : Nat := Nat.zero",
            "def «a.b» : Nat := Nat.zero",
            "def _root_.A.f : Nat := Nat.zero",
            "def _root_ : Nat := Nat.zero",
            "example : Nat := Nat.zero",
        ] {
            assert_eq!(expanded(src).unwrap(), None, "{src:?}");
        }
        // `ensureValidNamespace`: the last `_root_` after the prefix, named
        // up to itself.
        for (src, ns) in [
            ("def _root_.A._root_.f : Nat := Nat.zero", "A._root_"),
            ("def _root_._root_ : Nat := Nat.zero", "_root_"),
            (
                "def _root_.A._root_.B._root_.f : Nat := Nat.zero",
                "A._root_.B._root_",
            ),
        ] {
            match expanded(src) {
                Err(ElabError::InvalidNamespace(n)) => assert_eq!(n, ns, "{src:?}"),
                other => panic!("{src:?}: {other:?}"),
            }
        }
    }

    #[test]
    fn quoted_names_are_decoded() {
        // Oracle probes: `«gq»` admits `gq`; `.{«u»}` gives the level `u`;
        // `«a.b»` is ONE atomic component, admitted at the root.
        assert_eq!(name_of("def «gq» : Nat := Nat.zero"), comps(&["gq"]));
        let v = view_of("def gu2.{«u»} (α : Sort «u») (a : α) : α := a").unwrap();
        assert_eq!(v.univ_names, vec!["u".to_string()]);
        assert_eq!(name_of("def «a.b» : Nat := Nat.zero"), comps(&["a.b"]));
        assert_eq!(name_of("def a.«b» : Nat := Nat.zero"), comps(&["a", "b"]));
    }

    #[test]
    fn root_prefix_is_matched_by_component() {
        // Oracle probe: `def _root_x : Nat := Nat.zero` admits `_root_x`.
        assert_eq!(
            name_of("def _root_x : Nat := Nat.zero"),
            comps(&["_root_x"])
        );
        assert_eq!(
            expanded("def _root_x.f : Nat := Nat.zero")
                .unwrap()
                .map(|e| e.0),
            Some(vec!["_root_x".to_string()])
        );
        assert_eq!(name_of("def _root_ : Nat := Nat.zero"), comps(&["_root_"]));
    }

    #[test]
    fn self_reference_is_a_recursion_seam() {
        assert!(seam("def sr : Nat := sr").contains("recursive reference to `sr`"));
        assert!(seam("def sr : Nat := sr.foo").contains("recursive reference to `sr`"));
        assert!(seam("def sr : Nat := «sr»").contains("recursive reference to `sr`"));
        assert!(seam("def «sr» : Nat := sr").contains("recursive reference to `sr`"));
        // an unrelated identifier that merely starts with the name is not one
        assert!(view_of("def sr : Nat := srx").is_ok());
    }

    #[test]
    fn unsupported_value_forms_are_named_seams() {
        assert!(seam("def f : Nat → Nat\n  | n => n").contains("pattern-matching equations"));
        assert!(seam("def a : Nat := b\nwhere b := Nat.zero").contains("`where` declarations"));
        // `termination_by`/`decreasing_by` cannot be reached from source:
        // leanr's `Termination.suffix` is `opt(never()) opt(never())`
        // (`leanr_syntax/src/builtin/command.rs`), so `termination_by` lexes
        // as an identifier argument. See
        // `termination_hints_are_a_named_seam_on_a_synthetic_tree`.
        assert!(seam("def a : Nat := Nat.zero deriving Repr").contains("deriving"));
        assert!(seam("opaque o : Nat").contains("`opaque` without a value"));
        assert!(seam("def a b : Nat := Nat.zero").contains("bare binder identifier"));
    }

    /// The parser never fills `Termination.suffix`, so build the tree the
    /// real parser would give for a hint: a non-empty node in the suffix's
    /// first slot (substitution for the brief's `termination_by 1` source).
    #[test]
    fn termination_hints_are_a_named_seam_on_a_synthetic_tree() {
        let src = "def a : Nat := Nat.zero";
        let parsed = leanr_syntax::parse_module(src, &leanr_syntax::builtin::snapshot());
        assert!(parsed.errors.is_empty());
        let root = parsed.tree.root().clone_for_update();
        let kinds = &parsed.tree.kinds;
        let by_kind = |k: &str| {
            root.descendants()
                .find(|n| kinds.name(n.kind()) == k)
                .unwrap_or_else(|| panic!("no {k}"))
        };
        let suffix = by_kind("Lean.Parser.Termination.suffix");
        let slot = suffix.first_child().expect("hint slot");
        let hint = by_kind("Lean.Parser.Term.typeSpec")
            .clone_subtree()
            .clone_for_update();
        slot.splice_children(0..0, vec![NodeOrToken::Node(hint)]);
        let cmd = by_kind("Lean.Parser.Command.declaration");
        match DefView::from_syntax(&cmd, kinds) {
            Err(ElabError::UnsupportedSyntax(m)) => {
                assert!(m.contains("termination hints"), "{m}")
            }
            Err(e) => panic!("expected a named seam, got {e:?}"),
            Ok(_) => panic!("expected a named seam, got a view"),
        }
    }

    #[test]
    fn unsupported_commands_are_named_seams() {
        assert!(seam("instance : Wrap Nat := ⟨fun x => x⟩").contains("declaration kind"));
        assert!(seam("structure S where\n  x : Nat").contains("declaration kind"));
        assert!(seam("namespace Foo").contains("Lean.Parser.Command.namespace"));
        assert!(seam("#check Nat").ends_with(" — later M4"));
        assert!(seam("mutual\ndef a : Nat := Nat.zero\nend").ends_with(" — later M4"));
    }
}
