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
    ///
    /// M3b3 Task 5: NO LONGER PRODUCED. Imported `scoped` parser entries
    /// are now folded present-but-inactive (tagged with their activation
    /// namespace) instead of skipped, so `assemble` never records this
    /// reason anymore. The variant is retained (not deleted) as public
    /// API surface; nothing in-tree constructs it.
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
            // M3b3 Task 5: a `scoped` entry is no longer SKIPPED — it is
            // folded PRESENT-but-INACTIVE, tagged with its activation
            // namespace (`EntryScope::Scoped`'s decoded `NameId`), and
            // routed through the SAME `descr::interpret` the `Global` arm
            // uses. `ns` is `None` for `Global`, `Some(namespace)` for
            // `Scoped`; each sub-entry then picks the global or the scoped
            // builder method off it.
            let ns: Option<String> = match &entry.scope {
                EntryScope::Global => None,
                EntryScope::Scoped(ns_id) => Some(name_of(*ns_id)),
            };
            match &entry.entry {
                // A `scoped notation`'s atom is a SEPARATE `Scoped`
                // `Token` entry (empirically: `NotaDep.olean`'s `⊖⊖`), so
                // route it to scoped-token storage — an inactive scoped
                // atom must lex as an ident, not an `Atom`
                // (`StxScopedInactive` pin), which the always-active
                // `b.token(..)` table would break.
                ParserEntry::Token(t) => match &ns {
                    None => b.token(t),
                    Some(ns) => b.scoped_token(ns, t),
                },
                // Kinds/categories are grammar IDENTITY, not activation:
                // registered globally in both cases (the brief's DRAFT —
                // interning a node kind or declaring a category cannot be
                // "inactive"; only its productions/tokens gate on scope).
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
                            match &ns {
                                None => b.leading_prim(&cat_name, p),
                                Some(ns) => b.scoped_leading_prim(&cat_name, ns, p),
                            }
                        }
                        Ok(crate::descr::Interpreted::Trailing(p)) => {
                            b.category(&cat_name, Default::default());
                            match &ns {
                                None => b.trailing_prim(&cat_name, p),
                                Some(ns) => b.scoped_trailing_prim(&cat_name, ns, p),
                            }
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
