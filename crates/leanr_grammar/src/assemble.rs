use std::sync::Arc;

use leanr_kernel::bank::Store;
use leanr_kernel::Name;
use leanr_olean::ModuleData;
use leanr_syntax::grammar::GrammarSnapshot;

/// Why an imported entry was not folded into the snapshot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SkipReason {
    /// Constant has type `Parser`/`TrailingParser` (compiled function;
    /// shims are M3b3).
    RawParser,
    /// `ParserDescr.const/unary/binary` alias not in the table yet.
    UnknownAlias(String),
    /// Value is not a literal constructor tree we can walk.
    UnsupportedShape(&'static str),
    /// Referenced constant not present in the loaded closure.
    MissingConstant,
    /// Recursive `ParserDescr` reference cycle.
    Cycle,
    /// Scoped entry — activation semantics are M3b3.
    ScopedInactive,
}

/// A recorded skip: which declaration, and why.
#[derive(Clone, Debug)]
pub struct SkippedEntry {
    pub decl: String,
    pub reason: SkipReason,
}

/// The imported-base grammar for one import set.
pub struct AssembledGrammar {
    pub snapshot: GrammarSnapshot,
    pub skipped: Vec<SkippedEntry>,
}

/// Fold the closure's parser-extension entries (in closure order) onto
/// the builtin grammar. `modules` is `load_closure` output:
/// dependencies-first, each module once.
pub fn assemble(modules: &[(Arc<Name>, ModuleData)], store: &Store) -> AssembledGrammar {
    let _ = (modules, store);
    todo!("M3b2a Task 7")
}
