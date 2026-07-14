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
    /// `many1Indent` (do-blocks, tactic seqs) —
    /// Task 6 gives these their withPosition+colGe expansion.
    Many1Indent(Arc<Prim>),
    /// `sepByIndent`/`sepBy1Indent` (Extra.lean): `withPosition $ sepBy
    /// (checkColGe .. p) sep (psep <|> checkColEq .. checkLinebreakBefore
    /// .. pushNone) allowTrailingSep` (`..` standing in for the oracle's
    /// `>>` sequencing operator here, so a wrapped doc line never starts
    /// with it — rustdoc/clippy treat a LEADING `>` as a markdown
    /// blockquote marker). Task 9 generalizes this from a hardcoded-`";"`
    /// `SepByIndentSemicolon(Arc<Prim>)` (Task 6's original, never-
    /// registered placeholder — see `sep_by_indent`'s doc comment in
    /// parse.rs for the semantics it needed fixing once a real caller
    /// showed up) to a `sep`-parameterized primitive: every call site
    /// this port needs (`sepByIndentSemicolon`/`sepBy1IndentSemicolon`,
    /// hardcoding `sep = "; "`, AND `Term.structInstFields`'s own
    /// `sepByIndent .. ", " (allowTrailingSep := true)`, `sep = ", "`)
    /// shares the same underlying combinator in the oracle, differing
    /// only in `sep` and in `sepBy` vs. `sepBy1` (captured here as
    /// `min: 0` vs. `min: 1`) — `allowTrailingSep` is always `true` at
    /// every call site this port needs, so it isn't a separate field.
    SepByIndent {
        item: Arc<Prim>,
        sep: String,
        min: usize,
    },
    /// `withForbidden tk p` (Basic.lean) — Task 9: `doForDecl`'s
    /// iterable, `doIfCond`'s condition, `doUnless`/`termUnless`'s
    /// condition all wrap `termParser` in `withForbidden "do" ..` so the
    /// term Pratt-loop's application argument-loop can't swallow the
    /// construct's own trailing `"do "` keyword (`Term.do`'s own
    /// registered prec, `argPrec`, is exactly `ARG_PREC` — high enough
    /// to otherwise qualify as an `argument()`-strength trailing
    /// argument). See `parse.rs`'s `expect_atom` for the enforcement
    /// point (ORACLE-PORT `mkTokenAndFixPos`).
    WithForbidden(String, Arc<Prim>),
    /// `withoutForbidden p` — locally clears an enclosing
    /// `WithForbidden` scope (bracketing constructs like `(..)` have no
    /// parsing ambiguity to guard against internally).
    WithoutForbidden(Arc<Prim>),
    /// Zero-width success producing a `Syntax.missing` leaf (used by
    /// error recovery and a few builtin productions).
    EmitMissing,
    /// Zero-width success producing an EMPTY `Syntax.ident` leaf at the
    /// CURRENT position (no trivia skip first) — ORACLE-PORT
    /// `hygieneInfoFn` (Basic.lean): ``hygieneInfo`` always succeeds,
    /// fabricating an anonymous, empty-text `ident` positioned
    /// immediately after whatever token was just consumed (BEFORE its
    /// trailing whitespace — the oracle "steals" that trailing trivia
    /// for itself, but since our span only ever reports `(pos, pos)`
    /// for this zero-width leaf, not consuming any trivia here
    /// reproduces the observable position exactly; confirmed against a
    /// fresh oracle dump of `(  x)`, whose `hygieneInfo` ident sits at
    /// the byte offset immediately after `(`, not after the two
    /// following spaces). Used by `hygienicLParen` (paren/tuple/
    /// typeAscription/anonymousCtor's common `"(" >> hygieneInfo`
    /// prefix) and `letId`'s anaphoric-`let` fallback.
    EmitEmptyIdent,
    /// Raw single-character match that bypasses the LEXER entirely (no
    /// `next_token` call) — ORACLE-PORT `rawCh` (Basic.lean), used by
    /// `doubleQuotedName` (`` "`" >> checkNoWsBefore >> rawCh '`' >>
    /// ident ``): tokenizing normally at this position would let
    /// `next_token`'s unconditional `` ` ``-dispatch swallow the SECOND
    /// backtick plus the following ident into one `NameLit` token
    /// (indistinguishable from `` `foo ``'s own shape) — the whole
    /// reason the oracle comment says "we cannot use ``` "``" ``` as a
    /// new token either". Reading exactly one raw `char` straight from
    /// the source (like `FieldIdx`'s raw digit scan) sidesteps that
    /// ambiguity. Emits `KIND_ATOM` of the matched char's UTF-8 length;
    /// no leading-trivia skip (never needed: always reached right after
    /// a `CheckNoWsBefore`).
    RawChar(char),
    /// `Tactic.«unknown»`'s ENTIRE body — ORACLE-PORT `withPosition
    /// (ident >> errorAtSavedPos "unknown tactic" true)`
    /// (`Lean/Parser/Tactic.lean:29`), folded into one dedicated
    /// primitive rather than composed from `WithPosition` + `Ident` +
    /// a generic "push a diagnostic" combinator: `errorAtSavedPos`'s
    /// report needs the ident's OWN start byte offset, which is
    /// simplest to capture right at this call rather than threading a
    /// byte offset out through `WithPosition`'s (line, col)-only
    /// marker stack (`Ps::pos_stack`) — no other call site needs that
    /// byte offset today, so a parallel byte-offset marker stack
    /// purely to generalize this ONE row would be unused machinery.
    /// ALWAYS succeeds (an unrecognized tactic name is a recorded
    /// diagnostic, not a hard parse failure — this crate's `errors:
    /// Vec<ParseError>` models exactly that "parse errors are values"
    /// property; see the M3a builtin-surface spec's row for this
    /// production). See the interpreter arm in `parse.rs` for exactly
    /// which of `errorAtSavedPos`'s oracle semantics this reproduces
    /// and which it deliberately doesn't (Task 9 review finding 2).
    UnknownTacticIdent,
    /// `Lean.Parser.Command.docComment`'s body. ORACLE-PORT: `commentBody`
    /// is defined as a raw-scanning `Parser` value, `rawFn (finishCommentBlock
    /// (pushMissingOnError := true) (depth := one)) (trailingWs := true)`
    /// (Term.lean:69-70) — a raw, nesting-aware scan from the current
    /// position (AFTER the ordinary leading-trivia skip every `andthen`
    /// sequencing step performs — same mechanism as any other leaf token,
    /// see the interpreter arm) through the matching `-/`, INCLUSIVE,
    /// emitted as one `KIND_ATOM` leaf (never a further node-wrap of its
    /// own — same "leaf, not `leading_parser`" shape as `Ident`/`NumLit`).
    ///
    /// Task 10 (M3a): `docComment` itself is `leading_parser ppDedent $
    /// "/--" (then ppSpace, then ifVerso versoCommentBody commentBody,
    /// then ppLine)` — `doc.verso` defaults false, so every fixture takes
    /// the `commentBody`, never `versoCommentBody`, branch; `"/--"` is an
    /// ordinary `Prim::Symbol`, this primitive is only ever the SECOND
    /// child. Confirmed byte-for-byte against a fresh oracle dump of
    /// `/-- A doc comment. -/` (task-10 report): the `docComment` node's
    /// two children are `{"a":"/--","s":[9,12]}` then
    /// `{"a":"A doc comment. -/","s":[13,30]}` — note the span GAP
    /// (12→13): the space right after `/--` is the second atom's ordinary
    /// leading-trivia skip (an emitted `Whitespace` trivia event), NOT
    /// part of the comment-body atom's own span; the atom's text then
    /// runs through and includes the closing `-/`.
    DocCommentBody,
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
/// `sepBy1 .. (allowTrailingSep := true)` — the variant `Term.tuple`'s
/// inner list uses (source: `tuple := hygienicLParen >> optional (.. >>
/// termParser >> ", " >> sepBy1 termParser ", " (allowTrailingSep :=
/// true)) >> ")"`, Term.lean:186-187). NOT `Term.matchAlt`'s
/// comma-separated pattern groups — those are a PLAIN `sepBy1` with no
/// `allowTrailingSep` (Term.lean:266-267); see `match_alt` in
/// `builtin/term.rs`.
pub fn sep_by1_trailing(item: Prim, sep: &str) -> Prim {
    Prim::SepBy1 {
        item: Arc::new(item),
        sep: sep.to_string(),
        allow_trailing: true,
    }
}
/// `sepBy .. (allowTrailingSep := true)` — `Term.anonymousCtor`'s `⟨…⟩`
/// list (0 or more, source: `sepBy termParser ", " (allowTrailingSep :=
/// true)`).
pub fn sep_by_trailing(item: Prim, sep: &str) -> Prim {
    Prim::SepBy {
        item: Arc::new(item),
        sep: sep.to_string(),
        allow_trailing: true,
    }
}
/// Zero-width, ALWAYS-FAILING (never consumes) placeholder for a real
/// sub-grammar this port doesn't transcribe (documented "not ported"
/// slots — same idiom as `builtin/command.rs`'s `empty_opt()`, one
/// level lower: wrapping this in `opt(..)` reproduces an
/// always-empty-`null` oracle slot exactly, since a zero-`OrElse`
/// fails immediately without consuming, same as `Optional`'s clean
/// "nothing here" path).
pub fn never() -> Prim {
    Prim::OrElse(vec![])
}
/// `sepByIndent p sep (allowTrailingSep := true)` (Extra.lean) — 0-or-
/// more, indentation-scoped (see `Prim::SepByIndent`'s doc comment).
/// `Term.structInstFields`'s own call site (`sep = ", "`).
pub fn sep_by_indent(item: Prim, sep: &str) -> Prim {
    Prim::SepByIndent {
        item: Arc::new(item),
        sep: sep.to_string(),
        min: 0,
    }
}
/// `sepBy1Indent p sep (allowTrailingSep := true)` — 1-or-more variant;
/// `Term/Basic.lean`'s `tacticSeq1Indented` (`sep = ";"`) is the only
/// call site this port needs.
pub fn sep_by1_indent(item: Prim, sep: &str) -> Prim {
    Prim::SepByIndent {
        item: Arc::new(item),
        sep: sep.to_string(),
        min: 1,
    }
}
/// `withForbidden tk p` — see `Prim::WithForbidden`'s doc comment.
pub fn with_forbidden(tok: &str, p: Prim) -> Prim {
    Prim::WithForbidden(tok.to_string(), Arc::new(p))
}
pub fn without_forbidden(p: Prim) -> Prim {
    Prim::WithoutForbidden(Arc::new(p))
}
pub fn raw_char(c: char) -> Prim {
    Prim::RawChar(c)
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
    /// The module-header grammar (spec §Oracle harness / Task 7's
    /// vertical slice): `builtin::snapshot()` always sets this via
    /// `SnapshotBuilder::set_header`, so `parse_module` can `.expect()`
    /// it. `Option` (rather than a bare `Prim`) because a category-less
    /// test snapshot (`GrammarSnapshot::for_test`) has none — PF2
    /// resolution, task-7-brief.
    header: Option<Prim>,
}

impl GrammarSnapshot {
    pub fn kinds(&self) -> std::sync::Arc<crate::kind::KindInterner> {
        self.kinds.clone()
    }

    /// The module-header `Prim`, if this snapshot's builder set one
    /// (every real, `builtin::snapshot()`-built snapshot does).
    pub fn header_prim(&self) -> Option<Prim> {
        self.header.clone()
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
            header: None,
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
        SepByIndent { item, sep, min } => {
            h.update(&[33, *min as u8]);
            h.update(sep.as_bytes());
            h.update(b"\0");
            encode_prim(item, snap, h);
        }
        WithForbidden(tok, q) => {
            h.update(&[37]);
            h.update(tok.as_bytes());
            h.update(b"\0");
            encode_prim(q, snap, h);
        }
        WithoutForbidden(q) => {
            h.update(&[38]);
            encode_prim(q, snap, h);
        }
        EmitMissing => {
            h.update(&[34]);
        }
        EmitEmptyIdent => {
            h.update(&[35]);
        }
        RawChar(c) => {
            h.update(&[36]);
            let mut buf = [0u8; 4];
            h.update(c.encode_utf8(&mut buf).as_bytes());
        }
        UnknownTacticIdent => {
            h.update(&[39]);
        }
        DocCommentBody => {
            h.update(&[40]);
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
    header: Option<Prim>,
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
            header: None,
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

    /// Register a leading parser candidate with NO extra `Node` wrap —
    /// for productions whose oracle shape is a bare leaf (`Prim::Ident`,
    /// a `Syntax.ident`) or that already self-wrap (`Prim::NumLit`
    /// wraps itself in a "num" node via `Ps::lit`). `leading2` always
    /// adds an outer `Node { kind_name, .. }`, which would double-wrap
    /// either case — confirmed against a real oracle dump (Task 7):
    /// `x` is a bare `{"i":"x",...}`, `42` is `{"c":[...],"k":"num"}`
    /// with no further wrapper.
    pub fn leading_raw(&mut self, cat: &str, body: Prim) {
        self.harvest_tokens(&body);
        let f = first_tok(&body);
        let c = self
            .categories
            .get_mut(cat)
            .expect("category registered before leading_raw");
        let idx = c.leading_parsers.len();
        c.leading_parsers.push(body);
        c.leading.push((f, idx));
    }

    fn harvest_tokens(&mut self, p: &Prim) {
        let tokens = &mut self.tokens;
        walk_symbols(p, &mut |s| tokens.insert(s));
    }

    /// Set the module-header grammar (Task 7's vertical slice —
    /// `parse_module` reads this back via `GrammarSnapshot::header_prim`).
    /// Harvests `p`'s symbols into the token table exactly like
    /// `leading2`/`trailing2`, so header keywords (`prelude`, `import`,
    /// …) lex as `Atom`, not `Ident`.
    pub fn set_header(&mut self, p: Prim) {
        self.harvest_tokens(&p);
        self.header = Some(p);
    }

    pub fn finish(self) -> GrammarSnapshot {
        GrammarSnapshot {
            tokens: self.tokens,
            categories: self.categories,
            kinds: std::sync::Arc::new(self.kinds),
            header: self.header,
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
        | WithPosition(body)
        | WithoutForbidden(body) => first_tok(body),
        WithForbidden(_, body) => first_tok(body),
        Seq(ps) => ps
            .iter()
            .find(|q| !is_transparent_for_first(q))
            .map(first_tok)
            .unwrap_or(FirstTok::Any),
        Symbol(s) | NonReservedSymbol(s) => FirstTok::Sym(s.clone()),
        Ident | UnknownTacticIdent => FirstTok::Ident,
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
        SepByIndent { item, sep, .. } => {
            // The oracle's `sep` args (`"; "`/`", "`) carry a pretty-
            // print-only trailing space; `sep_by_indent` matches the
            // bare atom (no space to replicate), so THAT's what needs
            // registering as a real token — same trim `SepBy`/`SepBy1`
            // already apply to their own `sep` string just below.
            f(sep);
            walk_symbols(item, f);
        }
        // ORACLE-PORT `withForbidden`/`withoutForbidden` (Basic.lean):
        // both are `adaptCacheableContext ({ · with forbiddenTk?/
        // savedPos? := .. }) p` — i.e. `withFn (adaptCacheableContextFn
        // ..) p = { p with fn := .. }` (Types.lean `withFn`/
        // `adaptCacheableContext`). `info` (hence `collectTokens`) is
        // untouched — it's exactly `p.info`, forwarded unmodified. The
        // forbidden token string is NOT registered as a token by this
        // combinator (unlike `Symbol`'s `symbolInfo`, which explicitly
        // extends `collectTokens`); only `q`'s own reachable symbols
        // count. A prior version of this function harvested `tok` too —
        // harmless today ("do", the only real caller's forbidden token,
        // is harvested anyway via its own `sym("do")` elsewhere — see
        // `Term.do`), but a gratuitous divergence that would inject a
        // spurious token for any forbidden string that isn't otherwise a
        // symbol.
        WithForbidden(_tok, q) => walk_symbols(q, f),
        WithoutForbidden(q) => walk_symbols(q, f),
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
        | EmitMissing
        | EmitEmptyIdent
        | RawChar(_)
        | UnknownTacticIdent
        | DocCommentBody => {}
    }
}
