//! The parser as data (spec §Architecture / grammar): `Prim` is a
//! combinator tree the interpreter in `parse.rs` walks. Deliberately
//! ParserDescr-shaped: M3b maps `.olean`-decoded ParserDescr values
//! into this same enum, so builtin and user grammar run identically.
//! Builtin productions (builtin/*.rs) are Rust fns returning `Prim`.
//!
//! Task 6 adds categories + `GrammarSnapshot`: the Pratt-parsing
//! tables (`Category`, indexed by `FirstTok`), the `SnapshotBuilder`
//! that assembles them (interning kinds, harvesting token strings),
//! and the snapshot's stable `blake3` fingerprint (the M5 query-
//! firewall seam — spec §Architecture).

use std::sync::Arc;

use crate::kind::SyntaxKind;

#[derive(Clone, Debug)]
pub enum Prim {
    /// Sequence; children parse in order into the current node.
    Seq(Vec<Prim>),
    /// `leading_parser`: open node `kind`; `prec` gates against the
    /// category's right-binding power (None = always).
    Node {
        kind: SyntaxKind,
        prec: Option<u32>,
        body: Arc<Prim>,
    },
    /// `trailing_parser`: only legal as a category trailing entry.
    /// The already-parsed lhs becomes the node's first child (Pratt
    /// wrap); `lhs_prec` is the minimum lhs precedence.
    TrailingNode {
        kind: SyntaxKind,
        prec: u32,
        lhs_prec: u32,
        body: Arc<Prim>,
    },
    /// Expect this exact atom token (must be in the snapshot's table).
    Symbol(String),
    /// Ident that is RESERVED in the table but allowed here (Lean
    /// `nonReservedSymbol`, e.g. contextual keywords).
    NonReservedSymbol(String),
    Ident,
    /// Literal leaves — each wraps its token in the Lean node kind:
    /// "num", "scientific", "str", "char", "name".
    NumLit,
    ScientificLit,
    StrLit,
    CharLit,
    NameLit,
    /// Raw digit run after `.` (projections `x.1`) — Lean `fieldIdx`.
    FieldIdx,
    /// Recurse into a category at the given right-binding power.
    Category {
        name: String,
        rbp: u32,
    },
    Optional(Arc<Prim>),
    Many(Arc<Prim>),
    Many1(Arc<Prim>),
    /// Items + separator atoms interleaved flat in one `null` node.
    SepBy {
        item: Arc<Prim>,
        sep: String,
        allow_trailing: bool,
    },
    SepBy1 {
        item: Arc<Prim>,
        sep: String,
        allow_trailing: bool,
    },
    OrElse(Vec<Prim>),
    Atomic(Arc<Prim>),
    Lookahead(Arc<Prim>),
    NotFollowedBy(Arc<Prim>),
    /// Group results into a "group" node (Lean `group`).
    Group(Arc<Prim>),
    // --- position/precedence checks (Task 6 implements semantics) ---
    WithPosition(Arc<Prim>),
    CheckColGt,
    CheckColGe,
    CheckColEq,
    CheckLineEq,
    CheckPrec(u32),
    CheckLhsPrec(u32),
    CheckWsBefore,
    CheckNoWsBefore,
    /// `many1Indent` / `sepByIndent` (do-blocks, tactic seqs) —
    /// Task 6 gives these their withPosition+colGe expansion.
    Many1Indent(Arc<Prim>),
    SepByIndentSemicolon(Arc<Prim>),
    /// Zero-width success producing a `Syntax.missing` leaf (used by
    /// error recovery and a few builtin productions).
    EmitMissing,
}

// Terse constructors — builtin/*.rs is written in these.
pub fn seq(ps: impl IntoIterator<Item = Prim>) -> Prim {
    Prim::Seq(ps.into_iter().collect())
}
/// An always-fires `Node` (`prec: None`) — the common case;
/// precedence-gated nodes are built with the `Prim::Node` literal
/// directly (see `builtin`'s `leading_parser` definitions).
pub fn node(kind: SyntaxKind, body: Prim) -> Prim {
    Prim::Node {
        kind,
        prec: None,
        body: Arc::new(body),
    }
}
pub fn sym(s: &str) -> Prim {
    Prim::Symbol(s.to_string())
}
pub fn opt(p: Prim) -> Prim {
    Prim::Optional(Arc::new(p))
}
pub fn many(p: Prim) -> Prim {
    Prim::Many(Arc::new(p))
}
pub fn many1(p: Prim) -> Prim {
    Prim::Many1(Arc::new(p))
}
pub fn sep_by1(item: Prim, sep: &str) -> Prim {
    Prim::SepBy1 {
        item: Arc::new(item),
        sep: sep.to_string(),
        allow_trailing: false,
    }
}
pub fn or_else(ps: impl IntoIterator<Item = Prim>) -> Prim {
    Prim::OrElse(ps.into_iter().collect())
}
pub fn atomic(p: Prim) -> Prim {
    Prim::Atomic(Arc::new(p))
}
pub fn cat(name: &str, rbp: u32) -> Prim {
    Prim::Category {
        name: name.to_string(),
        rbp,
    }
}

// ============================================================
// Categories, `GrammarSnapshot`, fingerprint (Task 6).
// ============================================================

/// ORACLE-PORT `Init/Notation.lean` (the pin's actual home for the
/// `prec` macros — NOT `Init/Prelude.lean` as the task brief's inline
/// citation says; verified in the pinned toolchain source, values
/// match): `macro "max" : prec => `(prec| 1024)`, `"arg" => 1023`,
/// `"lead" => 1022`, `"min" => 10`.
pub const MAX_PREC: u32 = 1024;
pub const ARG_PREC: u32 = 1023;
pub const LEAD_PREC: u32 = 1022;
pub const MIN_PREC: u32 = 10;

/// What token class can begin a Prim — the category dispatch index
/// (Lean's `PrattParsingTables` leading/trailing token maps).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FirstTok {
    Sym(String),
    Ident,
    Num,
    Scientific,
    Str,
    Char,
    NameLit,
    /// Cannot be indexed (position checks, category recursion, …):
    /// tried on every dispatch, like Lean's non-indexed `leadingParsers`/
    /// `trailingParsers` lists.
    Any,
}

/// A syntax category's Pratt-parsing table: leading productions (the
/// atoms/prefixes that can START an expression) and trailing ones
/// (the infix/postfix continuations the trailing loop chains on).
/// Each list is paired with a first-token index of the SAME length
/// (`leading[i]`'s `usize` indexes `leading_parsers`) — `FirstTok::Any`
/// entries are simply tried on every dispatch, in registration order,
/// alongside whichever indexed entries matched (ORACLE-PORT
/// `PrattParsingTables`: `leadingTable` + always-tried `leadingParsers`,
/// `trailingTable` + always-tried `trailingParsers` — collapsed here
/// into one paired vector per side rather than two, since `dispatch`
/// just filters it).
#[derive(Clone, Debug, Default)]
pub struct Category {
    /// (first-token → candidate index) pairs, registration order.
    pub leading: Vec<(FirstTok, usize)>,
    pub leading_parsers: Vec<Prim>,
    pub trailing: Vec<(FirstTok, usize)>,
    pub trailing_parsers: Vec<Prim>,
}

/// The whole parser state as one explicit, hash-fingerprintable value
/// (spec §Architecture: the M5 query-firewall seam). Built once by
/// `SnapshotBuilder`, then read-only for the lifetime of every parse
/// run over it — `Ps` (parse.rs) borrows one of these instead of the
/// bare `TokenTable`/`KindInterner` pair Task 5 used as a placeholder.
#[derive(Debug)]
pub struct GrammarSnapshot {
    pub(crate) tokens: crate::lex::TokenTable,
    pub(crate) categories: std::collections::HashMap<String, Category>,
    kinds: std::sync::Arc<crate::kind::KindInterner>,
}

impl GrammarSnapshot {
    pub fn kinds(&self) -> std::sync::Arc<crate::kind::KindInterner> {
        self.kinds.clone()
    }

    /// Stable hash of the whole grammar (spec: the query-ready
    /// parser-state firewall fingerprint). Tokens are walked in the
    /// `TokenTable`'s own (`BTreeSet`, hence sorted) iteration order;
    /// categories are sorted by name; each category's Prims are
    /// encoded by a deterministic byte walk (`encode_prim`) — none of
    /// this depends on `HashMap`/interner insertion order, so two
    /// snapshots built by equivalent (not necessarily
    /// identically-ordered) `SnapshotBuilder` call sequences hash the
    /// same iff the grammars they describe are the same.
    pub fn fingerprint(&self) -> blake3::Hash {
        let mut h = blake3::Hasher::new();
        h.update(b"leanr-m3a-grammar-v1\0");
        for t in self.tokens.iter() {
            h.update(t.as_bytes());
            h.update(b"\0");
        }
        let mut names: Vec<_> = self.categories.keys().collect();
        names.sort();
        for name in names {
            h.update(name.as_bytes());
            h.update(b"\x01");
            let c = &self.categories[name];
            for p in c.leading_parsers.iter().chain(&c.trailing_parsers) {
                encode_prim(p, self, &mut h);
            }
        }
        h.finalize()
    }

    /// Test-only shim: wrap an already-built table/interner as a
    /// snapshot with no categories, so `parse.rs`'s toy-grammar tests
    /// (predating `Category`) keep working unchanged — `Ps` now always
    /// holds a `&GrammarSnapshot`, never a bare table+interner pair.
    #[cfg(test)]
    pub(crate) fn for_test(
        tokens: crate::lex::TokenTable,
        kinds: crate::kind::KindInterner,
    ) -> Self {
        GrammarSnapshot {
            tokens,
            categories: Default::default(),
            kinds: std::sync::Arc::new(kinds),
        }
    }
}

/// Deterministic `Prim` encoding: tag byte + fields; node/leaf kinds
/// are encoded by NAME (interner ids are session/build-relative, not
/// stable across snapshots) so the fingerprint depends only on the
/// grammar's observable shape. Every variant is handled explicitly —
/// no wildcard arm — so adding a `Prim` variant without extending this
/// is a compile error, not a silent fingerprint gap.
fn encode_prim(p: &Prim, snap: &GrammarSnapshot, h: &mut blake3::Hasher) {
    use Prim::*;
    match p {
        Seq(ps) => {
            h.update(&[0]);
            for q in ps {
                encode_prim(q, snap, h);
            }
            h.update(&[0xFF]);
        }
        Node { kind, prec, body } => {
            h.update(&[1]);
            h.update(snap.kinds.name(*kind).as_bytes());
            h.update(b"\0");
            h.update(&prec.unwrap_or(u32::MAX).to_le_bytes());
            encode_prim(body, snap, h);
        }
        TrailingNode {
            kind,
            prec,
            lhs_prec,
            body,
        } => {
            h.update(&[2]);
            h.update(snap.kinds.name(*kind).as_bytes());
            h.update(b"\0");
            h.update(&prec.to_le_bytes());
            h.update(&lhs_prec.to_le_bytes());
            encode_prim(body, snap, h);
        }
        Symbol(s) => {
            h.update(&[3]);
            h.update(s.as_bytes());
            h.update(b"\0");
        }
        NonReservedSymbol(s) => {
            h.update(&[4]);
            h.update(s.as_bytes());
            h.update(b"\0");
        }
        Ident => {
            h.update(&[5]);
        }
        NumLit => {
            h.update(&[6]);
        }
        ScientificLit => {
            h.update(&[7]);
        }
        StrLit => {
            h.update(&[8]);
        }
        CharLit => {
            h.update(&[9]);
        }
        NameLit => {
            h.update(&[10]);
        }
        FieldIdx => {
            h.update(&[11]);
        }
        Category { name, rbp } => {
            h.update(&[12]);
            h.update(name.as_bytes());
            h.update(b"\0");
            h.update(&rbp.to_le_bytes());
        }
        Optional(q) => {
            h.update(&[13]);
            encode_prim(q, snap, h);
        }
        Many(q) => {
            h.update(&[14]);
            encode_prim(q, snap, h);
        }
        Many1(q) => {
            h.update(&[15]);
            encode_prim(q, snap, h);
        }
        SepBy {
            item,
            sep,
            allow_trailing,
        } => {
            h.update(&[16, *allow_trailing as u8]);
            h.update(sep.as_bytes());
            h.update(b"\0");
            encode_prim(item, snap, h);
        }
        SepBy1 {
            item,
            sep,
            allow_trailing,
        } => {
            h.update(&[17, *allow_trailing as u8]);
            h.update(sep.as_bytes());
            h.update(b"\0");
            encode_prim(item, snap, h);
        }
        OrElse(ps) => {
            h.update(&[18]);
            for q in ps {
                encode_prim(q, snap, h);
            }
            h.update(&[0xFF]);
        }
        Atomic(q) => {
            h.update(&[19]);
            encode_prim(q, snap, h);
        }
        Lookahead(q) => {
            h.update(&[20]);
            encode_prim(q, snap, h);
        }
        NotFollowedBy(q) => {
            h.update(&[21]);
            encode_prim(q, snap, h);
        }
        Group(q) => {
            h.update(&[22]);
            encode_prim(q, snap, h);
        }
        WithPosition(q) => {
            h.update(&[23]);
            encode_prim(q, snap, h);
        }
        CheckColGt => {
            h.update(&[24]);
        }
        CheckColGe => {
            h.update(&[25]);
        }
        CheckColEq => {
            h.update(&[26]);
        }
        CheckLineEq => {
            h.update(&[27]);
        }
        CheckPrec(n) => {
            h.update(&[28]);
            h.update(&n.to_le_bytes());
        }
        CheckLhsPrec(n) => {
            h.update(&[29]);
            h.update(&n.to_le_bytes());
        }
        CheckWsBefore => {
            h.update(&[30]);
        }
        CheckNoWsBefore => {
            h.update(&[31]);
        }
        Many1Indent(q) => {
            h.update(&[32]);
            encode_prim(q, snap, h);
        }
        SepByIndentSemicolon(q) => {
            h.update(&[33]);
            encode_prim(q, snap, h);
        }
        EmitMissing => {
            h.update(&[34]);
        }
    }
}

/// Assembles a `GrammarSnapshot`: interns node kinds, harvests token
/// strings out of registered Prims into the token table, and indexes
/// leading/trailing parsers by their `FirstTok` for dispatch. Owns its
/// own `KindInterner` (the Task-1 bound — "never let user input drive
/// unbounded interning" — is upheld structurally: every `intern` call
/// this type makes happens while ASSEMBLING the grammar, never while
/// parsing source text; `Ps` (parse.rs) only ever *looks up* kinds by
/// name post-snapshot, it never interns).
pub struct SnapshotBuilder {
    kinds: crate::kind::KindInterner,
    tokens: crate::lex::TokenTable,
    categories: std::collections::HashMap<String, Category>,
}

impl SnapshotBuilder {
    pub fn new() -> Self {
        let mut kinds = crate::kind::KindInterner::new();
        // Literal node kinds the interpreter looks up by name (`lit`/
        // `field_idx` in parse.rs).
        for k in ["num", "scientific", "str", "char", "name", "fieldIdx"] {
            kinds.intern(k);
        }
        SnapshotBuilder {
            kinds,
            tokens: Default::default(),
            categories: Default::default(),
        }
    }

    pub fn kind(&mut self, name: &str) -> SyntaxKind {
        self.kinds.intern(name)
    }

    pub fn token(&mut self, tok: &str) {
        self.tokens.insert(tok);
    }

    pub fn category(&mut self, name: &str) {
        self.categories.entry(name.to_string()).or_default();
    }

    /// Register a leading parser: interns `kind_name`, wraps `body` in
    /// `Prim::Node`, harvests its `Symbol`s into the token table, and
    /// indexes the whole thing by its FIRST token for dispatch.
    pub fn leading2(&mut self, cat: &str, kind_name: &str, prec: u32, body: Prim) {
        let kind = self.kinds.intern(kind_name);
        let p = Prim::Node {
            kind,
            prec: Some(prec),
            body: Arc::new(body),
        };
        self.harvest_tokens(&p);
        let f = first_tok(&p);
        let c = self
            .categories
            .get_mut(cat)
            .expect("category registered before leading2");
        let idx = c.leading_parsers.len();
        c.leading_parsers.push(p);
        c.leading.push((f, idx));
    }

    /// Register a trailing parser (a category's Pratt-loop
    /// continuation): the already-parsed left-hand side becomes the
    /// node's first child (the "Pratt wrap" — parse.rs's `category`
    /// inserts the `Start` retroactively once this candidate wins).
    pub fn trailing2(&mut self, cat: &str, kind_name: &str, prec: u32, lhs: u32, body: Prim) {
        let kind = self.kinds.intern(kind_name);
        let p = Prim::TrailingNode {
            kind,
            prec,
            lhs_prec: lhs,
            body: Arc::new(body),
        };
        self.harvest_tokens(&p);
        let f = first_tok(&p);
        let c = self
            .categories
            .get_mut(cat)
            .expect("category registered before trailing2");
        let idx = c.trailing_parsers.len();
        c.trailing_parsers.push(p);
        c.trailing.push((f, idx));
    }

    fn harvest_tokens(&mut self, p: &Prim) {
        let tokens = &mut self.tokens;
        walk_symbols(p, &mut |s| tokens.insert(s));
    }

    pub fn finish(self) -> GrammarSnapshot {
        GrammarSnapshot {
            tokens: self.tokens,
            categories: self.categories,
            kinds: std::sync::Arc::new(self.kinds),
        }
    }
}

impl Default for SnapshotBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Convenience free functions so builtin grammar (Tasks 7-10) can read
/// `leading(&mut b, "term", "lit", MAX_PREC, Prim::Ident)` — cosmetic
/// wrappers over `SnapshotBuilder::leading2`/`trailing2` (kept as
/// distinct methods, not renamed, because Task 6's own tests call
/// `b.leading2(...)`/`b.trailing2(...)` directly — see the brief's
/// literal test source).
pub fn leading(b: &mut SnapshotBuilder, cat: &str, kind_name: &str, prec: u32, body: Prim) {
    b.leading2(cat, kind_name, prec, body);
}
pub fn trailing(
    b: &mut SnapshotBuilder,
    cat: &str,
    kind_name: &str,
    prec: u32,
    lhs: u32,
    body: Prim,
) {
    b.trailing2(cat, kind_name, prec, lhs, body);
}

/// FIRST-token of a Prim for dispatch indexing; `Any` when unknowable.
/// Looks through the "transparent" wrappers (`Node`/`TrailingNode`/
/// `Atomic`/`Group`/`WithPosition`) to their body, and through a `Seq`
/// to its first non-`is_transparent_for_first` element (position/prec
/// checks and lookaheads have no first token of their own — Lean's
/// `firstTokens` computation skips them the same way).
fn first_tok(p: &Prim) -> FirstTok {
    use Prim::*;
    match p {
        Node { body, .. }
        | TrailingNode { body, .. }
        | Atomic(body)
        | Group(body)
        | WithPosition(body) => first_tok(body),
        Seq(ps) => ps
            .iter()
            .find(|q| !is_transparent_for_first(q))
            .map(first_tok)
            .unwrap_or(FirstTok::Any),
        Symbol(s) | NonReservedSymbol(s) => FirstTok::Sym(s.clone()),
        Ident => FirstTok::Ident,
        NumLit => FirstTok::Num,
        ScientificLit => FirstTok::Scientific,
        StrLit => FirstTok::Str,
        CharLit => FirstTok::Char,
        NameLit => FirstTok::NameLit,
        _ => FirstTok::Any,
    }
}

/// Prims with no first token of their own — skipped when scanning a
/// `Seq` for its FIRST real token (position/precedence checks and
/// lookaheads never consume, so they can't anchor dispatch).
fn is_transparent_for_first(p: &Prim) -> bool {
    matches!(
        p,
        Prim::CheckPrec(_)
            | Prim::CheckLhsPrec(_)
            | Prim::CheckColGt
            | Prim::CheckColGe
            | Prim::CheckColEq
            | Prim::CheckLineEq
            | Prim::CheckWsBefore
            | Prim::CheckNoWsBefore
            | Prim::Lookahead(_)
            | Prim::NotFollowedBy(_)
    )
}

/// Recursive visitor over every `Symbol` literal and `SepBy`/`SepBy1`
/// separator string reachable from `p` — these are exactly the atoms
/// Lean's `syntax` elaboration registers as tokens (`collectTokens`),
/// so `SnapshotBuilder` harvests the same set into its `TokenTable`
/// when a leading/trailing parser is registered.
///
/// `NonReservedSymbol` is deliberately NOT harvested here — ORACLE-PORT
/// `nonReservedSymbolInfo` (Basic.lean:1143-1149) leaves `collectTokens`
/// at `ParserInfo`'s default (`id`, i.e. a no-op; Types.lean:499-500),
/// unlike `symbolInfo` (Basic.lean:1105-1108), which explicitly sets
/// `collectTokens := fun tks => sym :: tks`. The doc comment directly
/// above `nonReservedSymbolFnAux` spells out why: "registering it as a
/// token in a Term Syntax would not break the universe Parser" — e.g.
/// `max`/`imax` must still lex as plain `Ident` outside a `level`
/// category. Registering it here (as a prior version of this function
/// did) would make its text lex as `Atom` snapshot-wide, defeating
/// every contextual keyword. The `NonReservedSymbol` interpreter arm
/// (`expect_atom(s, true)` in parse.rs) matches its text against
/// `Ident` tokens directly, so it needs no table entry to work.
fn walk_symbols(p: &Prim, f: &mut impl FnMut(&str)) {
    use Prim::*;
    match p {
        Symbol(s) => f(s),
        NonReservedSymbol(_) => {}
        Seq(ps) | OrElse(ps) => {
            for q in ps {
                walk_symbols(q, f);
            }
        }
        Node { body, .. } | TrailingNode { body, .. } => walk_symbols(body, f),
        Optional(q) | Many(q) | Many1(q) | Atomic(q) | Lookahead(q) | NotFollowedBy(q)
        | Group(q) | WithPosition(q) | Many1Indent(q) => walk_symbols(q, f),
        SepByIndentSemicolon(q) => {
            // ORACLE-PORT `Term/Basic.lean` `sepByIndentSemicolon` hard-
            // codes its separator to `"; "`; parse.rs's `sep_by_indent`
            // matches the bare `;` character (no pretty-print-only
            // trailing space to replicate), so that's what needs
            // registering as a real token.
            f(";");
            walk_symbols(q, f);
        }
        SepBy { item, sep, .. } | SepBy1 { item, sep, .. } => {
            f(sep);
            walk_symbols(item, f);
        }
        Ident
        | NumLit
        | ScientificLit
        | StrLit
        | CharLit
        | NameLit
        | FieldIdx
        | Category { .. }
        | CheckColGt
        | CheckColGe
        | CheckColEq
        | CheckLineEq
        | CheckPrec(_)
        | CheckLhsPrec(_)
        | CheckWsBefore
        | CheckNoWsBefore
        | EmitMissing => {}
    }
}
