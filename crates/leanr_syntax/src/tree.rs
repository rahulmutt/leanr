//! Lossless green/red trees over rowan (spec §Architecture / tree).
//! Every source byte — trivia included — is a token in the tree, so
//! `text(parse(src)) == src` holds by construction. The parser emits a
//! flat `Event` list; `build_tree` folds it into a rowan green tree.
//! Events (not a live builder) because the Pratt machinery needs
//! speculation (truncate events) and trailing wraps (insert a Start),
//! neither of which rowan's `GreenNodeBuilder` supports directly.
//! This event layer is our trait-shaped boundary around rowan: if
//! rowan's model ever fights us, only `build_tree` changes (spec's
//! recorded escape hatch).

use std::sync::Arc;

use rowan::{GreenNode, GreenNodeBuilder};

use crate::kind::{KindInterner, SyntaxKind};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Lang {}

impl rowan::Language for Lang {
    type Kind = SyntaxKind;
    fn kind_from_raw(raw: rowan::SyntaxKind) -> SyntaxKind {
        SyntaxKind(raw.0)
    }
    fn kind_to_raw(kind: SyntaxKind) -> rowan::SyntaxKind {
        rowan::SyntaxKind(kind.0)
    }
}

pub type SyntaxNode = rowan::SyntaxNode<Lang>;
pub type SyntaxToken = rowan::SyntaxToken<Lang>;
pub use rowan::NodeOrToken;

/// Flat parse event. Token text is carried by (offset, len) into the
/// source — the builder slices the original `src`, which is what makes
/// losslessness structural rather than best-effort.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Event {
    Start(SyntaxKind),
    Token {
        kind: SyntaxKind,
        offset: u32,
        len: u32,
    },
    Finish,
    /// Lean `Syntax.missing` leaf (zero-width).
    Missing,
}

/// A parsed module: the green tree + the interner that names its kinds.
#[derive(Clone, Debug)]
pub struct SyntaxTree {
    pub green: GreenNode,
    pub kinds: Arc<KindInterner>,
}

impl SyntaxTree {
    pub fn root(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.green.clone())
    }

    /// The exact source text — byte-identical to the parser input.
    pub fn text(&self) -> String {
        self.root().text().to_string()
    }
}

/// Fold events into a green tree. `events` must be balanced
/// (Start/Finish match) and wrapped in exactly one root node — the
/// parser guarantees both; debug_asserts document the contract.
pub fn build_tree(src: &str, events: &[Event], kinds: Arc<KindInterner>) -> SyntaxTree {
    let mut builder = GreenNodeBuilder::new();
    let mut depth: i64 = 0;
    for ev in events {
        match ev {
            Event::Start(kind) => {
                builder.start_node(rowan::SyntaxKind(kind.0));
                depth += 1;
            }
            Event::Token { kind, offset, len } => {
                let s = *offset as usize;
                let e = s + *len as usize;
                builder.token(rowan::SyntaxKind(kind.0), &src[s..e]);
            }
            Event::Finish => {
                builder.finish_node();
                depth -= 1;
            }
            Event::Missing => {
                // Zero-width leaf; canonicalizes to {"k":"<missing>"}.
                builder.token(rowan::SyntaxKind(crate::kind::KIND_MISSING.0), "");
            }
        }
        debug_assert!(depth >= 0, "unbalanced Finish");
    }
    debug_assert_eq!(depth, 0, "unbalanced Start");
    SyntaxTree {
        green: builder.finish(),
        kinds,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kind::{KindInterner, KIND_ATOM, KIND_IDENT, KIND_WHITESPACE};

    /// Hand-build `def x` as (root (decl "def" WS ident)) and check
    /// byte-exact text() and tree shape.
    #[test]
    fn events_build_a_lossless_tree() {
        let src = "def x";
        let mut it = KindInterner::new();
        let root = it.intern("module");
        let decl = it.intern("Lean.Parser.Command.declaration");
        let events = vec![
            Event::Start(root),
            Event::Start(decl),
            Event::Token {
                kind: KIND_ATOM,
                offset: 0,
                len: 3,
            },
            Event::Token {
                kind: KIND_WHITESPACE,
                offset: 3,
                len: 1,
            },
            Event::Token {
                kind: KIND_IDENT,
                offset: 4,
                len: 1,
            },
            Event::Finish,
            Event::Finish,
        ];
        let tree = build_tree(src, &events, Arc::new(it));
        assert_eq!(tree.text(), src);
        let root_node = tree.root();
        assert_eq!(tree.kinds.name(root_node.kind()), "module");
        let decl_node = root_node.first_child().unwrap();
        assert_eq!(
            tree.kinds.name(decl_node.kind()),
            "Lean.Parser.Command.declaration"
        );
        assert_eq!(decl_node.children_with_tokens().count(), 3);
    }
}
