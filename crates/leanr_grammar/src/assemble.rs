use std::collections::HashMap;
use std::sync::Arc;

use leanr_kernel::bank::{NameId, Store};
use leanr_kernel::{ConstantInfo, Name};
use leanr_olean::{EntryScope, ModuleData, ParserEntry};
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
    // One constants map across the closure (parser decls may reference
    // descr constants from any dependency).
    let consts: HashMap<NameId, &ConstantInfo> = modules
        .iter()
        .flat_map(|(_, md)| md.constants.iter())
        .map(|c| (c.constant_val().name, c))
        .collect();

    let mut b = leanr_syntax::builtin::builder();
    let mut skipped = Vec::new();
    let name_of = |id: NameId| store.to_name(None, Some(id)).to_string();

    for (_module, md) in modules {
        for entry in &md.parser_entries {
            let e = match &entry.scope {
                EntryScope::Global => &entry.entry,
                EntryScope::Scoped(_) => {
                    if let ParserEntry::Parser { decl, .. } = &entry.entry {
                        skipped.push(SkippedEntry {
                            decl: name_of(*decl),
                            reason: SkipReason::ScopedInactive,
                        });
                    }
                    // Scoped token/category/kind entries are likewise
                    // inactive until M3b3; skip silently (nothing to name).
                    continue;
                }
            };
            match e {
                ParserEntry::Token(t) => b.token(t),
                ParserEntry::Kind(k) => {
                    b.kind(&name_of(*k));
                }
                ParserEntry::Category { cat, behavior, .. } => {
                    b.category(&name_of(*cat), map_behavior(*behavior));
                }
                ParserEntry::Parser { cat, decl } => {
                    let cat_name = name_of(*cat);
                    match crate::descr::interpret(*decl, &consts, store, &mut b) {
                        Ok(crate::descr::Interpreted::Leading(p)) => {
                            b.category(&cat_name, Default::default()); // ensure exists (idempotent)
                            b.leading_prim(&cat_name, p);
                        }
                        Ok(crate::descr::Interpreted::Trailing(p)) => {
                            b.category(&cat_name, Default::default());
                            b.trailing_prim(&cat_name, p);
                        }
                        Err(reason) => skipped.push(SkippedEntry {
                            decl: name_of(*decl),
                            reason,
                        }),
                    }
                }
            }
        }
    }
    AssembledGrammar {
        snapshot: b.finish(),
        skipped,
    }
}

fn map_behavior(b: leanr_olean::CatBehavior) -> leanr_syntax::grammar::LeadingIdentBehavior {
    use leanr_syntax::grammar::LeadingIdentBehavior as L;
    match b {
        leanr_olean::CatBehavior::Default => L::Default,
        leanr_olean::CatBehavior::Symbol => L::Symbol,
        leanr_olean::CatBehavior::Both => L::Both,
    }
}
