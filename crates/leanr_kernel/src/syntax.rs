use std::fmt;
use std::sync::Arc;

use crate::{Name, Nat};

/// Substring slice (oracle: Init/Prelude.lean:3582, `Substring.Raw`).
/// `startPos`/`stopPos` are `String.Pos.Raw`, a single-field structure
/// over `byteIdx : Nat` (Init/Prelude.lean:3557); a single-field struct
/// is represented as the field itself, so each is just a `Nat`.
#[derive(Debug, Clone)]
pub struct Substring {
    pub str: String,
    pub start_pos: Nat,
    pub stop_pos: Nat,
}

/// Source position metadata on syntax (oracle: Init/Prelude.lean:4827,
/// `SourceInfo`). `None` is fieldless. Non-self-recursive, so the
/// derived `Debug` is depth-safe.
#[derive(Debug, Clone)]
pub enum SourceInfo {
    Original {
        leading: Substring,
        pos: Nat,
        trailing: Substring,
        end_pos: Nat,
    },
    Synthetic {
        pos: Nat,
        end_pos: Nat,
        canonical: bool,
    },
    None,
}

/// A possible binding of an identifier in a quotation (oracle:
/// Init/Prelude.lean:4930, `Syntax.Preresolved`). Non-self-recursive;
/// its `Arc<Name>` fields have a depth-safe `Debug`, so the derive is
/// safe.
#[derive(Debug, Clone)]
pub enum Preresolved {
    Namespace(Arc<Name>),
    Decl {
        name: Arc<Name>,
        fields: Vec<String>,
    },
}

/// Lean syntax tree (oracle: Init/Prelude.lean:4943, `Syntax`). The
/// `kind` field is `SyntaxNodeKind := Name` (Init/Prelude.lean:4919).
///
/// `Syntax` is `Arc`-recursive through `Node.args`, so — like `Expr` —
/// `Drop` is iterative (explicit stack) and `Debug` is manual and
/// non-recursive: node depth is attacker-controlled (`.olean` bytes are
/// untrusted) and recursing would overflow the stack.
pub enum Syntax {
    Missing,
    Node {
        info: SourceInfo,
        kind: Arc<Name>,
        args: Vec<Arc<Syntax>>,
    },
    Atom {
        info: SourceInfo,
        val: String,
    },
    Ident {
        info: SourceInfo,
        raw_val: Substring,
        val: Arc<Name>,
        preresolved: Vec<Preresolved>,
    },
}

/// Manual (non-derived) impl: never recurses into `Arc<Syntax>` children
/// (crate precedent: see `Expr`/`Name`), so it stays safe on
/// adversarially deep chains. Children render as `..` placeholders.
impl fmt::Debug for Syntax {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Syntax::Missing => f.write_str("Syntax::Missing"),
            Syntax::Node {
                info,
                kind,
                args: _,
            } => write!(
                f,
                "Syntax::Node {{ info: {:?}, kind: {:?}, args: .. }}",
                info, kind
            ),
            Syntax::Atom { info, val } => {
                write!(f, "Syntax::Atom {{ info: {:?}, val: {:?} }}", info, val)
            }
            Syntax::Ident {
                info,
                raw_val,
                val,
                preresolved,
            } => write!(
                f,
                "Syntax::Ident {{ info: {:?}, raw_val: {:?}, val: {:?}, preresolved: {:?} }}",
                info, raw_val, val, preresolved
            ),
        }
    }
}

impl Drop for Syntax {
    fn drop(&mut self) {
        let mut stack: Vec<Arc<Syntax>> = Vec::new();
        take_syntax_children(self, &mut stack);
        while let Some(node) = stack.pop() {
            if let Ok(mut owned) = Arc::try_unwrap(node) {
                take_syntax_children(&mut owned, &mut stack);
            }
        }
    }
}

fn take_syntax_children(s: &mut Syntax, stack: &mut Vec<Arc<Syntax>>) {
    if let Syntax::Node { args, .. } = s {
        stack.append(args);
    }
}
