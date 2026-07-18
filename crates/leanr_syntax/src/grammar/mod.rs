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

pub mod alias;
pub mod notation;
pub mod overlay;
pub(crate) mod scope;
pub mod surface;
pub use notation::{
    derive_delta, mangle_kind, GrammarDelta, NamingCtx, NotationAtom, NotationSpec,
};
pub use overlay::{CategoryDelta, Overlay};

/// M3b3 Task 4: a grammar entry's ACTIVATION scope — the tag that
/// decides, at each grammar read point, whether a same-file (overlay)
/// or imported (Task 5) production/token is currently in force. Task 5
/// reuses this enum + `ScopeStack::is_active` verbatim for imported
/// entries.
///
/// Dump-pinned (`StxScoped.lean`/`StxScopedInactive.lean`, elaborating
/// dumper): a plain `syntax`/`notation` is `Global` even when declared
/// inside a `namespace` (only its KIND NAME is namespace-qualified —
/// `StxNamespace.lean`'s top-level `#check wobns` after `end Widgetish`
/// still lexes `wobns` as an atom and parses via `Widgetish.termWobns`);
/// `scoped` ties activation to its declaring namespace; `local` ties it
/// to its declaring scope depth.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpecScope {
    /// Always active (plain `syntax`/`notation`/`mixfix`, and every
    /// builtin base production).
    Global,
    /// `scoped` — active iff its namespace is in the active set (a
    /// prefix of the current namespace path, or an explicit `open`).
    /// Its `String` is the CURRENT namespace at the declaration site
    /// (dump-pinned: `scoped syntax "wobsc"` inside `namespace Widgsc`
    /// derives `Scoped("Widgsc")`, active under `namespace Widgsc`,
    /// `open Widgsc`, and `namespace Widgsc.Inner`).
    Scoped(String),
    /// `local` — active while the exact scope entry that declared it is
    /// still live. `anchor` is the id of the INNERMOST scope entry at the
    /// declaration site (`ScopeStack::innermost_id()`), or `None` when
    /// declared at top level (active for the rest of the file). M3b3
    /// Task 6b replaced the earlier `scope_len` depth capture: keying on
    /// a never-reused entry id (not depth) matches the oracle, which does
    /// NOT re-activate a popped `local` when an unrelated later scope
    /// reaches the same depth (`StxLocalInactive.lean`; the
    /// `local_activation_anchors_to_its_declaring_scope` pin test).
    Local { anchor: Option<u64> },
}

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
    ///
    /// `sep` below is the BARE atom `sep_by_indent`'s interpreter
    /// actually `expect_atom`s against — every one of the oracle
    /// citations above quotes the SOURCE parameter, which carries a
    /// pretty-print-only trailing space (`"; "`/`", "`); the space is
    /// never part of the matched token (ordinary trivia takes it
    /// instead), so every builder (`sep_by_indent`/`sep_by1_indent`'s own
    /// callers in `builtin/tactic.rs`/`builtin/term.rs`, and `alias.rs`'s
    /// `sepByIndentSemicolon`/`sepBy1IndentSemicolon`) passes the trimmed
    /// `";"`, matching `walk_symbols`'s own `SepByIndent` arm comment
    /// (M3b3 Task 9: a first draft of the `alias.rs` entries used `"; "`
    /// here and a fresh oracle dump caught the resulting span mismatch —
    /// `StxSepIndent.stx.jsonl`'s `#check` line spans the bare `;`
    /// alone).
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
    /// ORACLE `incQuotDepth p` (`Term.quot`/`Tactic.quot`/`Command.quot`/
    /// `Term.dynamicQuot` all wrap their body in this): body parses with
    /// quotation depth +1 (antiquotation alternatives become active —
    /// engine-level, Task 3).
    IncQuotDepth(Arc<Prim>),
    /// ORACLE `decQuotDepth p`: the `$(e)` nested-term escape parses its
    /// body one level shallower (saturating at 0). Not reached by any
    /// M3b2b Task 2 fixture (no antiquots yet — Task 3) but plumbed now
    /// alongside `IncQuotDepth` per the brief's interface contract.
    DecQuotDepth(Arc<Prim>),
    /// ORACLE `Term.dynamicQuot := withoutPosition <| leading_parser
    /// "`(" >> ident >> "| " >> incQuotDepth (parserOfStack 1) >> ")"`'s
    /// `ident >> "| " >> incQuotDepth (parserOfStack 1)` tail: consume an
    /// ident naming a category, then `|`, then that category's parser at
    /// depth+1. Engine-special because the category is named by input
    /// text (precedent: `UnknownTacticIdent`, `DocCommentBody`).
    DynamicQuotBody,
    /// ORACLE `many1Unbox p := withResultOf (many1NoAntiquot p) fun stx
    /// => if stx.getNumArgs == 1 then stx.getArg 0 else stx` (Basic.lean)
    /// — `Command.quot`'s command-list body (`Command.lean:50-51`,
    /// doc comment: "Multiple commands will be put in a `null` node, but
    /// a single command will not"). Not one of the brief's headline 3
    /// interface variants — a genuinely NEW empirical pin the Step 1
    /// dump forced (see `term_quot.rs`'s module doc): `many1(p)` (the
    /// existing combinator) always wraps in `null` regardless of count,
    /// which doesn't match the dump's 3-child `Command.quot` node for a
    /// single `#check`. `first_tokens`/`walk_symbols` treat this exactly
    /// like `Many1` (mandatory ≥1 occurrence, same token/symbol
    /// forwarding) — only the tree SHAPE differs, in `run`'s arm.
    Many1Unbox(Arc<Prim>),
    /// ORACLE `leading_parser (withAnonymousAntiquot := false) ..`
    /// (`Term.lean`'s `basicFun`/`letId`/`letIdDecl`/… and friends): the
    /// wrapped parser's own antiquot alternative(s), if any, may not
    /// accept a BARE `$x` (no `:name` suffix) — only a typed `$x:name`.
    /// Threaded through `parse.rs`'s `Ps::anon_antiquot_ok` flag (M3b2b
    /// Task 3). No builtin production constructs this yet — the pinned
    /// toolchain's `leading_parser (withAnonymousAntiquot := false)`
    /// macro sugar sets a PLAIN `Bool` field on the `leadingNode`/
    /// `nodeWithAntiquot` call it expands to, rather than wrapping an
    /// arbitrary sub-parser the way this primitive does; that shape
    /// isn't reachable from any M3b2b Task 1-3 builtin fixture. Plumbed
    /// now (exhaustive match arms below, plus `encode`/`walk_symbols`)
    /// per the Task 3 brief's interface contract, but currently
    /// UNPRODUCED: Task 4's imported-`ParserDescr.nodeWithAntiquot`
    /// mapping (`leanr_grammar::descr`) concluded the toolchain's
    /// `compileParserDescr` hardcodes `anonymous := true`
    /// unconditionally for that constructor — no decoded OLean entry
    /// ever builds this wrap (`descr.rs`'s own doc comment on that arm;
    /// pinned by `wrap_bracket_notation_stays_an_unwrapped_node`).
    WithoutAnonymousAntiquot(Arc<Prim>),
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
/// ORACLE `many1Unbox` — see `Prim::Many1Unbox`'s doc comment.
pub fn many1_unbox(p: Prim) -> Prim {
    Prim::Many1Unbox(Arc::new(p))
}
pub fn inc_quot_depth(p: Prim) -> Prim {
    Prim::IncQuotDepth(Arc::new(p))
}
pub fn dec_quot_depth(p: Prim) -> Prim {
    Prim::DecQuotDepth(Arc::new(p))
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
/// slots): wrapping this in `opt(..)` reproduces an always-empty-
/// `null` oracle slot exactly, since a zero-`OrElse` fails immediately
/// without consuming, same as `Optional`'s clean "nothing here" path.
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

/// ORACLE-PORT `Lean.Parser.LeadingIdentBehavior` (`Basic.lean`,
/// `indexed`): how a category's leading-token dispatch treats an
/// actual identifier token whose text happens to match a registered
/// literal key (e.g. a `nonReservedSymbol`-keyed row like
/// `Attr.extern`'s `"extern"`).
///
/// - `Default` — ORACLE semantics (`indexed`'s `.default` arm,
///   Basic.lean:1707): always dispatch only the generic `Ident`-keyed
///   candidates; a literal-text key match is never consulted (`find
///   identKind` unconditionally) — the oracle's `TokenMap` never even
///   looks the ident's own text up as a key in this mode.
///
///   THIS PORT'S `dispatch` (parse.rs) does not implement that literally:
///   its `FirstTok::Sym(s)` arm matches an `Ident`-kind token whenever
///   `s == text`, unconditionally — i.e. regardless of `ident_behavior`,
///   including under `Default`. That is a real divergence from the
///   oracle's own stated `.default` semantics, and it is DELIBERATE, not
///   an oversight (M3a Task 11 item (c) — a prior version of this doc
///   bullet contradicted the code by describing only the oracle
///   semantics without saying so): it is safe on the ported surface only
///   because the ONE call site that can actually reach a `Sym`-keyed
///   entry via an `Ident`-kind token under `Default` behavior is
///   `Prim::NonReservedSymbol` (`level`'s `max`/`imax`,
///   `Level.lean:27,29`, both `includeIdent := true`). The oracle
///   achieves the identical outcome by literally dual-registering such a
///   production under BOTH the literal-text key AND the generic
///   `identKind` key (`nonReservedSymbolInfo`'s `.tokens [sym, "ident"]`,
///   Basic.lean:1144-1149) — `.default`'s `find identKind` picks it up
///   via the SECOND registration, never needing to consult the first.
///   This port instead does no dual build-time registration for
///   `NonReservedSymbol` at all (`first_tokens`'s own doc comment,
///   `walk_symbols`'s doc comment) and reproduces the same reachability
///   at DISPATCH time via that always-on `Sym`-vs-`Ident`-text-match arm.
///   For every OTHER `Default`-behavior category's real `Prim::Symbol`
///   rows, the arm is a dead branch: any text actually harvested into
///   the token table (`walk_symbols`) always lexes as `Atom`, never
///   `Ident` (maximal-munch prefers the exact keyword), so `kind ==
///   Ident && s == text` can never hold for them — see `dispatch`'s own
///   doc comment at the `FirstTok::Sym` match arm for the lexing
///   argument in full.
/// - `Symbol` — if a literal-text key match exists, run ONLY those
///   candidates (the generic `Ident`-keyed ones are not even tried);
///   otherwise fall back to the generic `Ident`-keyed candidates.
/// - `Both` — union the literal-text key match (if any) with the
///   generic `Ident`-keyed candidates.
///
/// Each builtin category's value is read off its own
/// `registerBuiltinParserAttribute`/`registerBuiltinParserAttribute`
/// call site in the pin (the `behavior` parameter defaults to
/// `.default` when omitted): `attr` = `.symbol` (`Attr.lean:20`);
/// `tactic` = `.both` (`Term/Basic.lean:33`); `prio` = `.both`
/// (`Attr.lean:16`); `level`/`term`/`command`/`doElem`/
/// `structInstFieldDecl` all omit the parameter, hence `.default`
/// (`Level.lean:17`, `Extension.lean:590,595`, `Do.lean:16`,
/// `Term/Basic.lean:272`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum LeadingIdentBehavior {
    #[default]
    Default,
    Symbol,
    Both,
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
    /// ORACLE-PORT `ParserCategory.behavior` — see
    /// `LeadingIdentBehavior`'s own doc comment.
    pub ident_behavior: LeadingIdentBehavior,
    /// M3b3 Task 5: imported `scoped` productions folded into this
    /// category, PRESENT-but-INACTIVE. Each entry carries its own
    /// first-token index (`FirstTok`, same `index_entries` computation as
    /// the always-active `leading`/`trailing` above), its already-shaped
    /// `Prim` (`Node`/`TrailingNode`, exactly like `leading_prim`), and
    /// its activation namespace (`String`) — the current namespace at the
    /// declaration site, decoded from the olean's `EntryScope::Scoped`.
    /// `parse.rs`'s `category()` read path iterates these ALONGSIDE the
    /// base tables but only admits an entry while
    /// `ps.scope.is_active(&SpecScope::Scoped(ns))` — the SAME predicate
    /// same-file overlay `scoped` entries go through (`dispatch_overlay`).
    /// A separate short vec so the hot (no-scoped-entries) path pays
    /// nothing: `category()` only iterates it when non-empty. Never the
    /// always-active `leading`/`trailing` tables — a `scoped` production
    /// must not dispatch until its namespace is opened.
    pub scoped_leading: Vec<(FirstTok, Prim, String)>,
    pub scoped_trailing: Vec<(FirstTok, Prim, String)>,
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
    /// M3b3 Task 5: every imported `scoped` token paired with its
    /// activation namespace `(token, ns)`, in registration order. The
    /// PARALLEL of `Overlay::token_scopes` for the imported base: a
    /// `scoped` notation's atom must NOT enter the always-active `tokens`
    /// table above (an inactive one would then lex as an `Atom` instead
    /// of an ident — the same-file `StxScopedInactive` pin forbids that),
    /// so it lives here instead and `Ps` (parse.rs) folds only the
    /// currently-active ones into its lexer view via
    /// `rebuild_active_overlay_tokens`. Empty for every scoped-free
    /// (pre-M3b3) snapshot, so the fingerprint and lexer behavior are
    /// byte-identical there.
    pub(crate) scoped_tokens: Vec<(String, String)>,
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

    /// Number of interned kinds = first free dynamic slot for the
    /// overlay (M3b1: `Overlay::new` numbers its own kinds starting
    /// here, so overlay kind ids never collide with the base's).
    pub fn kind_count(&self) -> u16 {
        self.kinds.len_u16()
    }

    /// The module-header `Prim`, if this snapshot's builder set one
    /// (every real, `builtin::snapshot()`-built snapshot does).
    pub fn header_prim(&self) -> Option<Prim> {
        self.header.clone()
    }

    /// M3b3 Task 5: the set of activation namespaces carried by the
    /// imported `scoped` entries folded into this snapshot — collected
    /// across every category's `scoped_leading`/`scoped_trailing` plus
    /// the snapshot-level `scoped_tokens`. Present-but-inactive: a member
    /// namespace only brings its entries into force once a same-file
    /// `open`/`namespace` activates it (`ScopeStack::is_active`). Empty
    /// for every scoped-free snapshot (`builtin::snapshot()`, and any
    /// import set with no `scoped` notations). Read-only query seam —
    /// `leanr_grammar`'s assemble tests assert an imported `scoped`
    /// notation lands here tagged with its namespace rather than in the
    /// always-active tables.
    pub fn scoped_namespaces(&self) -> std::collections::BTreeSet<String> {
        let mut out = std::collections::BTreeSet::new();
        for c in self.categories.values() {
            for (_, _, ns) in c.scoped_leading.iter().chain(&c.scoped_trailing) {
                out.insert(ns.clone());
            }
        }
        for (_, ns) in &self.scoped_tokens {
            out.insert(ns.clone());
        }
        out
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
        // v2: bumped from v1 when `Category::ident_behavior`
        // (`LeadingIdentBehavior`) was added to the hashed shape below —
        // a grammar that only differs in a category's ident-dispatch
        // behavior must fingerprint differently (M3a Task 10 review
        // Finding 1).
        h.update(b"leanr-m3a-grammar-v2\0");
        for t in self.tokens.iter() {
            h.update(t.as_bytes());
            h.update(b"\0");
        }
        // M3b3 Task 5: imported `scoped` tokens participate in grammar
        // identity too (a snapshot that only differs in a scoped token or
        // its namespace must fingerprint differently). Appended AFTER the
        // always-active `tokens` loop above with no domain-version bump:
        // a scoped-free snapshot has an empty `scoped_tokens`, so this
        // adds zero bytes and its fingerprint is byte-identical to
        // pre-M3b3 (the M3b2a import goldens' guard).
        for (tok, ns) in &self.scoped_tokens {
            h.update(tok.as_bytes());
            h.update(b"\0");
            h.update(ns.as_bytes());
            h.update(b"\0");
        }
        let mut names: Vec<_> = self.categories.keys().collect();
        names.sort();
        for name in names {
            h.update(name.as_bytes());
            h.update(b"\x01");
            let c = &self.categories[name];
            let behavior_byte: u8 = match c.ident_behavior {
                LeadingIdentBehavior::Default => 0,
                LeadingIdentBehavior::Symbol => 1,
                LeadingIdentBehavior::Both => 2,
            };
            h.update(&[behavior_byte]);
            let kind_name = |k: SyntaxKind| self.kinds.name(k).to_string();
            for p in c.leading_parsers.iter().chain(&c.trailing_parsers) {
                encode_prim(p, &kind_name, &mut h);
            }
            // M3b3 Task 5: imported `scoped` productions, each followed by
            // its activation namespace. Empty `scoped_leading`/
            // `scoped_trailing` (every scoped-free category) contributes
            // zero bytes here — byte-identical to pre-M3b3, same rationale
            // as `scoped_tokens` above.
            for (_, p, ns) in c.scoped_leading.iter().chain(&c.scoped_trailing) {
                encode_prim(p, &kind_name, &mut h);
                h.update(ns.as_bytes());
                h.update(b"\0");
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
            scoped_tokens: Vec::new(),
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
///
/// `kind_name` resolves a `SyntaxKind` to its stable name — a closure
/// rather than a bare `&GrammarSnapshot` so this ONE recursive walk is
/// shared by both `GrammarSnapshot::fingerprint` (resolves via its own
/// `KindInterner`) and `Overlay::fingerprint_into` (M3b1 Task 5;
/// resolves via the overlay's own `kind_names`, which a `GrammarSnapshot`
/// knows nothing about) — no parallel copy of this match in `overlay.rs`.
pub(crate) fn encode_prim(
    p: &Prim,
    kind_name: &dyn Fn(SyntaxKind) -> String,
    h: &mut blake3::Hasher,
) {
    use Prim::*;
    match p {
        Seq(ps) => {
            h.update(&[0]);
            for q in ps {
                encode_prim(q, kind_name, h);
            }
            h.update(&[0xFF]);
        }
        Node { kind, prec, body } => {
            h.update(&[1]);
            h.update(kind_name(*kind).as_bytes());
            h.update(b"\0");
            h.update(&prec.unwrap_or(u32::MAX).to_le_bytes());
            encode_prim(body, kind_name, h);
        }
        TrailingNode {
            kind,
            prec,
            lhs_prec,
            body,
        } => {
            h.update(&[2]);
            h.update(kind_name(*kind).as_bytes());
            h.update(b"\0");
            h.update(&prec.to_le_bytes());
            h.update(&lhs_prec.to_le_bytes());
            encode_prim(body, kind_name, h);
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
            encode_prim(q, kind_name, h);
        }
        Many(q) => {
            h.update(&[14]);
            encode_prim(q, kind_name, h);
        }
        Many1(q) => {
            h.update(&[15]);
            encode_prim(q, kind_name, h);
        }
        SepBy {
            item,
            sep,
            allow_trailing,
        } => {
            h.update(&[16, *allow_trailing as u8]);
            h.update(sep.as_bytes());
            h.update(b"\0");
            encode_prim(item, kind_name, h);
        }
        SepBy1 {
            item,
            sep,
            allow_trailing,
        } => {
            h.update(&[17, *allow_trailing as u8]);
            h.update(sep.as_bytes());
            h.update(b"\0");
            encode_prim(item, kind_name, h);
        }
        OrElse(ps) => {
            h.update(&[18]);
            for q in ps {
                encode_prim(q, kind_name, h);
            }
            h.update(&[0xFF]);
        }
        Atomic(q) => {
            h.update(&[19]);
            encode_prim(q, kind_name, h);
        }
        Lookahead(q) => {
            h.update(&[20]);
            encode_prim(q, kind_name, h);
        }
        NotFollowedBy(q) => {
            h.update(&[21]);
            encode_prim(q, kind_name, h);
        }
        Group(q) => {
            h.update(&[22]);
            encode_prim(q, kind_name, h);
        }
        WithPosition(q) => {
            h.update(&[23]);
            encode_prim(q, kind_name, h);
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
            encode_prim(q, kind_name, h);
        }
        SepByIndent { item, sep, min } => {
            h.update(&[33, *min as u8]);
            h.update(sep.as_bytes());
            h.update(b"\0");
            encode_prim(item, kind_name, h);
        }
        WithForbidden(tok, q) => {
            h.update(&[37]);
            h.update(tok.as_bytes());
            h.update(b"\0");
            encode_prim(q, kind_name, h);
        }
        WithoutForbidden(q) => {
            h.update(&[38]);
            encode_prim(q, kind_name, h);
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
        IncQuotDepth(q) => {
            h.update(&[41]);
            encode_prim(q, kind_name, h);
        }
        DecQuotDepth(q) => {
            h.update(&[42]);
            encode_prim(q, kind_name, h);
        }
        DynamicQuotBody => {
            h.update(&[43]);
        }
        Many1Unbox(q) => {
            h.update(&[44]);
            encode_prim(q, kind_name, h);
        }
        WithoutAnonymousAntiquot(q) => {
            h.update(&[45]);
            encode_prim(q, kind_name, h);
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
    /// M3b3 Task 5: imported `scoped` tokens harvested here (with their
    /// activation namespace) instead of into `tokens` above — see
    /// `GrammarSnapshot::scoped_tokens`.
    scoped_tokens: Vec<(String, String)>,
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
            scoped_tokens: Vec::new(),
            header: None,
        }
    }

    pub fn kind(&mut self, name: &str) -> SyntaxKind {
        self.kinds.intern(name)
    }

    pub fn token(&mut self, tok: &str) {
        self.tokens.insert(tok);
    }

    pub fn category(&mut self, name: &str, behavior: LeadingIdentBehavior) {
        self.categories
            .entry(name.to_string())
            .or_insert_with(|| Category {
                ident_behavior: behavior,
                ..Default::default()
            });
    }

    /// Register a leading parser: interns `kind_name`, wraps `body` in
    /// `Prim::Node`, harvests its `Symbol`s into the token table, and
    /// indexes the whole thing by every first token it can start with
    /// (Task 11 item (a) — see `index_entries`/`first_tokens`).
    pub fn leading2(&mut self, cat: &str, kind_name: &str, prec: u32, body: Prim) {
        let kind = self.kinds.intern(kind_name);
        let p = Prim::Node {
            kind,
            prec: Some(prec),
            body: Arc::new(body),
        };
        self.harvest_tokens(&p);
        let fs = index_entries(&p);
        let c = self
            .categories
            .get_mut(cat)
            .expect("category registered before leading2");
        let idx = c.leading_parsers.len();
        c.leading_parsers.push(p);
        for f in fs {
            c.leading.push((f, idx));
        }
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
        let fs = index_entries(&p);
        let c = self
            .categories
            .get_mut(cat)
            .expect("category registered before trailing2");
        let idx = c.trailing_parsers.len();
        c.trailing_parsers.push(p);
        for f in fs {
            c.trailing.push((f, idx));
        }
    }

    /// Register an already-shaped leading production — unlike
    /// `leading2`, `prim` arrives pre-wrapped (M3b2a Task 4: an
    /// interpreted, imported `ParserDescr`'s own `node` constructor
    /// already produced the `Prim::Node`, so wrapping it again here
    /// would double-wrap it). Otherwise identical to `leading2`: harvest
    /// its `Symbol`s into the token table, index it by every first token
    /// it can start with, and push it onto the category's
    /// `leading_parsers` list.
    ///
    /// M3b3 Task 8: also harvests any `SepBy`/`SepBy1` separator's
    /// antiquot-splice-suffix token (`sepby_suffix_tokens`) — an
    /// IMPORTED production with a non-`,` separator (e.g. a Mathlib
    /// `syntax .. sepBy(p, "|")`) needs its own `"|*"` registered the
    /// same way a same-file declaration does (`Overlay::register`),
    /// or the same silent-misparse gap `builtin/mod.rs`'s `",*"`
    /// comment documents would reopen for every imported separator.
    pub fn leading_prim(&mut self, cat: &str, prim: Prim) {
        self.harvest_tokens(&prim);
        self.harvest_sepby_suffix_tokens(&prim);
        let fs = index_entries(&prim);
        let c = self
            .categories
            .get_mut(cat)
            .expect("category registered before leading_prim");
        let idx = c.leading_parsers.len();
        c.leading_parsers.push(prim);
        for f in fs {
            c.leading.push((f, idx));
        }
    }

    /// Trailing counterpart of [`Self::leading_prim`] — `prim` arrives
    /// already `Prim::TrailingNode`-wrapped; otherwise identical to
    /// `trailing2`, plus the same M3b3 Task 8 suffix-token harvest.
    pub fn trailing_prim(&mut self, cat: &str, prim: Prim) {
        self.harvest_tokens(&prim);
        self.harvest_sepby_suffix_tokens(&prim);
        let fs = index_entries(&prim);
        let c = self
            .categories
            .get_mut(cat)
            .expect("category registered before trailing_prim");
        let idx = c.trailing_parsers.len();
        c.trailing_parsers.push(prim);
        for f in fs {
            c.trailing.push((f, idx));
        }
    }

    /// M3b3 Task 5: register an imported `scoped` LEADING production —
    /// the present-but-inactive twin of [`Self::leading_prim`]. `prim`
    /// arrives already `Prim::Node`-wrapped (an interpreted imported
    /// `ParserDescr`); `ns` is its activation namespace (the current
    /// namespace at the declaration site, decoded from the olean's
    /// `EntryScope::Scoped`). Unlike `leading_prim`, its `Symbol`s are
    /// harvested into `scoped_tokens` (with `ns`) — NOT the always-active
    /// `tokens` table — so an inactive scoped notation's atom lexes as an
    /// ident, exactly like the same-file `StxScopedInactive` pin (see
    /// `GrammarSnapshot::scoped_tokens`). The production itself lands in
    /// the category's `scoped_leading` (never `leading`/`leading_parsers`)
    /// so `category()`'s read path only admits it while `ns` is active.
    ///
    /// M3b3 Task 8: a scoped production's `SepBy`/`SepBy1` suffix token
    /// must be scope-filtered exactly like its own separator — harvested
    /// into `scoped_tokens` under the SAME `ns`, not the always-active
    /// table, or an inactive scoped `sepBy` production's suffix token
    /// would leak into lexing while the scope is off.
    pub fn scoped_leading_prim(&mut self, cat: &str, ns: &str, prim: Prim) {
        self.harvest_scoped_tokens(ns, &prim);
        self.harvest_scoped_sepby_suffix_tokens(ns, &prim);
        let fs = index_entries(&prim);
        let c = self
            .categories
            .get_mut(cat)
            .expect("category registered before scoped_leading_prim");
        for f in fs {
            c.scoped_leading.push((f, prim.clone(), ns.to_string()));
        }
    }

    /// Trailing counterpart of [`Self::scoped_leading_prim`] — `prim`
    /// arrives already `Prim::TrailingNode`-wrapped; lands in the
    /// category's `scoped_trailing`. Same activation/token-scoping story,
    /// including the M3b3 Task 8 scoped suffix-token harvest.
    pub fn scoped_trailing_prim(&mut self, cat: &str, ns: &str, prim: Prim) {
        self.harvest_scoped_tokens(ns, &prim);
        self.harvest_scoped_sepby_suffix_tokens(ns, &prim);
        let fs = index_entries(&prim);
        let c = self
            .categories
            .get_mut(cat)
            .expect("category registered before scoped_trailing_prim");
        for f in fs {
            c.scoped_trailing.push((f, prim.clone(), ns.to_string()));
        }
    }

    /// M3b3 Task 5: record an imported `scoped` `ParserEntry::Token`
    /// under its activation namespace `ns` — the scoped twin of
    /// [`Self::token`]. A `scoped notation`'s olean carries its atom as a
    /// SEPARATE `Scoped` `Token` entry (confirmed by decoding
    /// `NotaDep.olean`: `Token("⊖⊖")` and `Parser{..}` are BOTH `Scoped`),
    /// so it must go here — not the always-active `tokens` table — or an
    /// inactive scoped atom would wrongly lex as an `Atom`.
    pub fn scoped_token(&mut self, ns: &str, tok: &str) {
        self.scoped_tokens.push((tok.to_string(), ns.to_string()));
    }

    fn harvest_scoped_tokens(&mut self, ns: &str, p: &Prim) {
        let scoped = &mut self.scoped_tokens;
        walk_symbols(p, &mut |s| scoped.push((s.to_string(), ns.to_string())));
    }

    /// M3b3 Task 8: the always-active twin of
    /// [`Self::harvest_scoped_sepby_suffix_tokens`] — folds
    /// `sepby_suffix_tokens`'s derived suffix tokens (if any) into the
    /// always-active token table, called alongside `harvest_tokens` by
    /// [`Self::leading_prim`]/[`Self::trailing_prim`].
    fn harvest_sepby_suffix_tokens(&mut self, p: &Prim) {
        let mut suffixes = Vec::new();
        sepby_suffix_tokens(p, &mut suffixes);
        for s in &suffixes {
            self.tokens.insert(s);
        }
    }

    /// M3b3 Task 8: scoped twin of [`Self::harvest_sepby_suffix_tokens`]
    /// — folds `sepby_suffix_tokens`'s derived suffix tokens into
    /// `scoped_tokens` under `ns`, exactly like `harvest_scoped_tokens`
    /// does for the bare separator itself.
    fn harvest_scoped_sepby_suffix_tokens(&mut self, ns: &str, p: &Prim) {
        let mut suffixes = Vec::new();
        sepby_suffix_tokens(p, &mut suffixes);
        for s in suffixes {
            self.scoped_tokens.push((s, ns.to_string()));
        }
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
        let fs = index_entries(&body);
        let c = self
            .categories
            .get_mut(cat)
            .expect("category registered before leading_raw");
        let idx = c.leading_parsers.len();
        c.leading_parsers.push(body);
        for f in fs {
            c.leading.push((f, idx));
        }
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
            scoped_tokens: self.scoped_tokens,
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

/// ORACLE-PORT `Lean.Parser.FirstTokens` (`Types.lean:459-495`): the
/// static "what can this production start with" lattice the oracle
/// computes per-`Parser` (as `ParserInfo.firstTokens`) and consults in
/// `addLeadingParser`/`addTrailingParserAux` (`Extension.lean:106-132`)
/// to decide how — or whether — to index a registered production.
/// Task 11 item (a): our port previously only ever produced a single
/// `FirstTok` (effectively always collapsing to `Unknown`'s `Any`
/// bucket the moment an `Optional`/`Many`/etc. showed up), so any
/// production whose body opened with an optional prefix (`declaration`,
/// `section`, …) went completely unindexed — `recover_command` (and
/// every other Pratt dispatch) then had to try it unconditionally,
/// which for the "sweep to the next command keyword" recovery heuristic
/// meant those keywords were never recognized as command starts at all.
/// This enum is the oracle's lattice ported directly, so `Category`'s
/// index can hold every token a production can *actually* lead with,
/// exactly as the oracle's `TokenMap` does.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Ft {
    /// `FirstTokens.epsilon` — matches without consuming anything (a
    /// true `epsilonInfo` combinator: `checkPrec`/`checkLhsPrec`/
    /// `checkColGe`/`checkWsBefore`/`checkNoWsBefore`, and this crate's
    /// own always-succeeding zero-width leaves `EmitMissing`/
    /// `EmitEmptyIdent`). Acts as `seq`'s left identity and `merge`'s
    /// "make the other side optional" case.
    Epsilon,
    /// `FirstTokens.unknown` — cannot be statically bounded (the
    /// oracle's *default* `ParserInfo.firstTokens`, `Types.lean:502`;
    /// every combinator that doesn't explicitly override it lands
    /// here). Dominates `seq` (poisons the rest of the sequence, mirrors
    /// `| tks, _ => tks` catching `Unknown` on the left) and `merge`
    /// (any pairing not otherwise matched falls to `_,_ => unknown`).
    Unknown,
    /// `FirstTokens.tokens tks` — definitely starts with one of these.
    Tokens(Vec<FirstTok>),
    /// `FirstTokens.optTokens tks` — MAY start with one of these (the
    /// rest of the production can also just be absent). Still indexed
    /// under every token in `tks` exactly like `Tokens` — the oracle's
    /// `addLeadingParser`/`addTrailingParserAux` (`Extension.lean:
    /// 117-122`, `:129-131`) route BOTH the `tokens` and `optTokens`
    /// arms through the identical `addTokens tks` call; only `Category`'s
    /// OWN combinators (`seq`/`merge`) ever distinguish the two.
    OptTokens(Vec<FirstTok>),
}

impl Ft {
    /// ORACLE-PORT `FirstTokens.toOptional` (`Types.lean:475-477`).
    fn into_optional(self) -> Ft {
        match self {
            Ft::Tokens(tks) => Ft::OptTokens(tks),
            other => other,
        }
    }

    /// ORACLE-PORT `FirstTokens.seq` (`Types.lean:468-473`) — the
    /// `andthen`/`>>` (sequencing) combinator's `firstTokens` (`p.seq
    /// q`, `andthenInfo`, `Basic.lean:97`). Order matters: patterns are
    /// tried top-to-bottom exactly as in the oracle, so e.g. `(Unknown,
    /// Unknown)` falls through every specific arm to the final
    /// catch-all (`tks, _ => tks`) rather than accidentally matching an
    /// earlier one.
    fn seq(self, other: Ft) -> Ft {
        match (self, other) {
            (Ft::Epsilon, tks) => tks,
            (Ft::OptTokens(mut s1), Ft::OptTokens(s2)) => {
                s1.extend(s2);
                Ft::OptTokens(ft_dedup(s1))
            }
            (Ft::OptTokens(mut s1), Ft::Tokens(s2)) => {
                s1.extend(s2);
                Ft::Tokens(ft_dedup(s1))
            }
            (Ft::OptTokens(_), Ft::Unknown) => Ft::Unknown,
            (tks, _) => tks,
        }
    }

    /// ORACLE-PORT `FirstTokens.merge` (`Types.lean:479-487`) — the
    /// `orelse`/`<|>` (choice) combinator's `firstTokens` (`p.merge q`,
    /// `orelseInfo`, `Basic.lean:272`).
    fn merge(self, other: Ft) -> Ft {
        match (self, other) {
            (Ft::Epsilon, tks) => tks.into_optional(),
            (tks, Ft::Epsilon) => tks.into_optional(),
            (Ft::Tokens(mut s1), Ft::Tokens(s2)) => {
                s1.extend(s2);
                Ft::Tokens(ft_dedup(s1))
            }
            (Ft::OptTokens(mut s1), Ft::OptTokens(s2)) => {
                s1.extend(s2);
                Ft::OptTokens(ft_dedup(s1))
            }
            (Ft::Tokens(mut s1), Ft::OptTokens(s2)) => {
                s1.extend(s2);
                Ft::OptTokens(ft_dedup(s1))
            }
            (Ft::OptTokens(mut s1), Ft::Tokens(s2)) => {
                s1.extend(s2);
                Ft::OptTokens(ft_dedup(s1))
            }
            _ => Ft::Unknown,
        }
    }
}

/// Order-preserving de-dup (`FirstTok` has no `Ord`, so this is a plain
/// `O(n^2)` scan — every list here is a handful of keyword tokens, not
/// user-scale data).
fn ft_dedup(v: Vec<FirstTok>) -> Vec<FirstTok> {
    let mut out: Vec<FirstTok> = Vec::with_capacity(v.len());
    for f in v {
        if !out.contains(&f) {
            out.push(f);
        }
    }
    out
}

/// `Prim` → `Ft`: the oracle-ported computation `SnapshotBuilder` runs
/// once per registered production (see `index_entries`, its only
/// caller). Each arm cites the oracle combinator whose `ParserInfo`
/// construction it reproduces; combinators with no explicit
/// `firstTokens` override in the oracle default to `Ft::Unknown`
/// (`ParserInfo`'s own default, `Types.lean:502`) — spelled out
/// per-arm below rather than left to a wildcard, so a future `Prim`
/// variant added without a matching arm here is a compile error, not a
/// silent misindex (same discipline `encode_prim` already uses).
fn first_tokens(p: &Prim) -> Ft {
    use Prim::*;
    match p {
        // `node`/`trailingNode`/`group` (`nodeInfo`) and `atomic`/
        // `lookahead` (`withFn`, which only replaces `fn`, leaving
        // `info` — hence `firstTokens` — untouched) all forward the
        // wrapped parser's own `firstTokens` unchanged.
        Node { body, .. }
        | TrailingNode { body, .. }
        | Group(body)
        | Atomic(body)
        | Lookahead(body) => first_tokens(body),
        // `withPosition`/`withoutPosition` (`withFn`) and `withForbidden`/
        // `withoutForbidden` (`adaptCacheableContext`, which is also a
        // pure `withFn`-shaped context tweak — `info` untouched, see
        // `walk_symbols`'s own doc comment on the same pair) all forward
        // unchanged too.
        WithPosition(body) | WithoutForbidden(body) => first_tokens(body),
        WithForbidden(_, body) => first_tokens(body),
        Seq(ps) => {
            let mut it = ps.iter();
            match it.next() {
                None => Ft::Epsilon,
                Some(first) => it.fold(first_tokens(first), |acc, q| acc.seq(first_tokens(q))),
            }
        }
        OrElse(ps) => {
            let mut it = ps.iter();
            match it.next() {
                // `never()`'s empty `OrElse` — only ever appears wrapped
                // in `Optional` (see its own doc comment), whose
                // `into_optional` leaves `Unknown` as `Unknown` regardless,
                // so this is never actually observed as a top-level
                // registration's own `Ft`.
                None => Ft::Unknown,
                Some(first) => it.fold(first_tokens(first), |acc, q| acc.merge(first_tokens(q))),
            }
        }
        // `symbolInfo`/`nonReservedSymbolInfo` (`Basic.lean:1105-1108,
        // 1143-1149`): `FirstTokens.tokens [sym]`. (`nonReservedSymbolInfo`
        // additionally unions in a generic `"ident"` key when
        // `includeIdent`, which this port instead reproduces at DISPATCH
        // time — `parse.rs`'s `dispatch` matches a `FirstTok::Sym` entry
        // against an `Ident`-kind token with equal text too — see
        // `LeadingIdentBehavior::Default`'s doc comment for why that's
        // the right seam, not this one.)
        Symbol(s) | NonReservedSymbol(s) => Ft::Tokens(vec![FirstTok::Sym(s.clone())]),
        // `mkAtomicInfo`/`identNoAntiquot` etc. (`Basic.lean:1243-1300`):
        // `FirstTokens.tokens ["ident"/"num"/...]` — one synthetic key
        // per literal kind, same as this port's dedicated `FirstTok`
        // variants. `UnknownTacticIdent` folds `withPosition (ident >>
        // errorAtSavedPos ..)` into one primitive (see its own doc
        // comment); `errorAtSavedPos`'s bare `{ fn := .. }` info is
        // `Unknown`, but `ident`'s mandatory `Tokens(["ident"])` seq'd
        // with it still dominates (`seq`'s final catch-all), so the
        // whole production is `Tokens([Ident])` — computed directly here
        // rather than via a literal `ident >> errorAtSavedPos` expansion,
        // since this primitive never actually decomposes that way at
        // runtime either (see the `parse.rs` interpreter arm).
        Ident | UnknownTacticIdent => Ft::Tokens(vec![FirstTok::Ident]),
        NumLit => Ft::Tokens(vec![FirstTok::Num]),
        ScientificLit => Ft::Tokens(vec![FirstTok::Scientific]),
        StrLit => Ft::Tokens(vec![FirstTok::Str]),
        CharLit => Ft::Tokens(vec![FirstTok::Char]),
        NameLit => Ft::Tokens(vec![FirstTok::NameLit]),
        // `fieldIdxFn`/raw-digit leaves have no oracle `ParserInfo`
        // override of their own kind in this port's shape (never
        // registered as a leading/trailing candidate in its own right —
        // always reached deep inside an already-dispatched `Term.proj`)
        // — conservatively `Unknown`.
        FieldIdx => Ft::Unknown,
        // Category recursion (`Term.parser`/`categoryParser`): the
        // oracle's own category-invoking combinator sets no
        // `firstTokens` override, so it's `Unknown` by the same default
        // every un-overridden combinator gets.
        Category { .. } => Ft::Unknown,
        // `optionalInfo` (`Basic.lean:373`): `p.firstTokens.toOptional`.
        Optional(q) => first_tokens(q).into_optional(),
        // `manyNoAntiquot`'s `noFirstTokenInfo` (`Basic.lean:428-431`):
        // sets `collectTokens`/`collectKinds` but leaves `firstTokens` at
        // `ParserInfo`'s own default — deliberately `Unknown`, NOT
        // `toOptional` (unlike `optional`) — `many(p)` can match zero
        // times, and the oracle gives up bounding it entirely rather
        // than keeping `p`'s own tokens as an `optTokens` candidate.
        Many(_) => Ft::Unknown,
        // `many1NoAntiquot := withFn many1Fn` (`Basic.lean:438`): `info`
        // (hence `firstTokens`) is forwarded from `p` unchanged — `many1`
        // requires ≥1 occurrence, so `p`'s own first token is mandatory.
        Many1(q) => first_tokens(q),
        // `sepByInfo` (`Basic.lean:476-479`): no `firstTokens` field set
        // ⇒ default `Unknown` (can match zero items, same reasoning as
        // `many`).
        SepBy { .. } => Ft::Unknown,
        // `sepBy1Info` (`Basic.lean:481-485`): `firstTokens := p.firstTokens`
        // (mandatory ≥1 item; `sep` never contributes since it can only
        // ever follow an already-parsed item).
        SepBy1 { item, .. } => first_tokens(item),
        // `notFollowedByFn`'s wrapper (`Basic.lean:408-409`) is built via
        // bare `where fn := ..` — no `info :=` at all, so `firstTokens`
        // is `ParserInfo`'s own default: `Unknown` (testing an upcoming
        // parser's ABSENCE cannot itself be indexed by that parser's
        // tokens — the whole point is it succeeds on anything else).
        NotFollowedBy(_) => Ft::Unknown,
        // `checkPrecFn`/`checkLhsPrecFn`/`checkColGeFn` all construct
        // `info := epsilonInfo` explicitly (`Basic.lean:164-165,175-176,
        // 1499-1500`).
        CheckPrec(_) | CheckLhsPrec(_) | CheckColGe => Ft::Epsilon,
        // `checkColGtFn`/`checkColEqFn`/`checkLineEqFn` (`Basic.lean:
        // 1466-1481, 1503-1525, 1527-1543`) build their `Parser` via bare
        // `where fn := ..`/`{ fn := .. }` with NO `info` override —
        // `ParserInfo`'s own default, `Unknown` (NOT `epsilonInfo`,
        // despite all four being "zero-width position checks" in
        // spirit — confirmed by reading the pin directly, since this is
        // exactly the kind of easy-to-assume-uniform detail that would
        // otherwise silently mis-port: an `Unknown` heading a `Seq`
        // poisons the WHOLE production to unindexed, unlike `Epsilon`,
        // which defers to what follows).
        CheckColGt | CheckColEq | CheckLineEq => Ft::Unknown,
        // `checkWsBefore`/`checkNoWsBefore` (`Basic.lean:1184-1186,
        // 1221-1223`) both construct `info := epsilonInfo` explicitly.
        CheckWsBefore | CheckNoWsBefore => Ft::Epsilon,
        // `many1Indent p = withPosition $ many1 (checkColGe .. >> p)`
        // (`Extra.lean:190-191`): `withPosition`/`many1` both forward
        // unchanged, `checkColGe` is `Epsilon` ⇒ `seq` defers to `p`.
        Many1Indent(q) => first_tokens(q),
        // `sepByIndent`/`sepBy1Indent` (`Extra.lean:202-208`): both
        // `withPosition $ sepBy(1) (checkColGe .. >> item) sep ..` —
        // `min == 0` mirrors bare `sepBy` (`Unknown`, can be empty);
        // `min >= 1` mirrors `sepBy1` (`checkColGe` is `Epsilon`, defers
        // to `item`, mandatory).
        SepByIndent { item, min: 0, .. } => {
            let _ = item;
            Ft::Unknown
        }
        SepByIndent { item, .. } => first_tokens(item),
        // `hygieneInfoNoAntiquot`'s `nodeInfo hygieneInfoKind epsilonInfo`
        // (`Basic.lean:1348`): forwards `epsilonInfo` unchanged.
        // `EmitMissing` is this port's analogous always-succeeding,
        // zero-width leaf (no direct oracle `Parser` value of its own —
        // see its doc comment) — same `Epsilon` shape.
        EmitMissing | EmitEmptyIdent => Ft::Epsilon,
        // `rawCh` bypasses the lexer/token table entirely and (per its
        // own doc comment) is never reached at the head of a registered
        // production — conservatively `Unknown`.
        RawChar(_) => Ft::Unknown,
        // `commentBody`'s raw scan leaf is likewise never its own
        // registered production's head (always the second child after a
        // literal `"/--"` `Symbol`, which already dominates the
        // production's `Ft` via `seq`'s catch-all) — `Unknown` is a safe,
        // never-exercised default.
        DocCommentBody => Ft::Unknown,
        // `incQuotDepth`/`decQuotDepth` (`Basic.lean`) are both
        // `adaptCacheableContextFn`-shaped `withFn` wrappers (like
        // `withPosition`/`withForbidden` above) — `info` (hence
        // `firstTokens`) forwards from the inner parser unchanged.
        IncQuotDepth(q) | DecQuotDepth(q) => first_tokens(q),
        // `dynamicQuot`'s own `ident >> "| " >> ..` head is a mandatory
        // `ident` — same `Tokens([Ident])` shape as `UnknownTacticIdent`
        // above, for the same reason (folded into one primitive, but the
        // ident is still the unconditional first token).
        DynamicQuotBody => Ft::Tokens(vec![FirstTok::Ident]),
        // `many1Unbox p := withResultOf (many1NoAntiquot p) ..`
        // (Basic.lean): `withResultOfInfo` rebuilds a FRESH `ParserInfo`
        // carrying only `collectTokens`/`collectKinds` from `p` — NOT
        // `firstTokens`, which is left at `ParserInfo`'s own default,
        // `Unknown` (see `Prim::Many1Unbox`'s doc comment for the full
        // citation). Never actually the head of a registered production
        // in this port anyway (`Command.quot` always precedes it with a
        // literal `"`("` `Symbol`, which already dominates via `seq`'s
        // catch-all) — `Unknown` is the oracle-faithful answer either way.
        Many1Unbox(_) => Ft::Unknown,
        // `leading_parser (withAnonymousAntiquot := false) ..` sets a
        // plain flag on the SAME `leadingNode`/`nodeWithAntiquot` call —
        // no separate `withFn`/`info` wrap of its own in the oracle —
        // so this port's stand-in wrapper (see the variant's own doc
        // comment) forwards the inner parser's `firstTokens` unchanged,
        // same as every other pure-scoping wrapper above (`WithPosition`,
        // `WithForbidden`, `IncQuotDepth`/`DecQuotDepth`).
        WithoutAnonymousAntiquot(q) => first_tokens(q),
    }
}

/// The `(FirstTok, idx)` index entries a freshly-registered production
/// should occupy, computed from its `Ft` (Task 11 item (a)). `Tokens`/
/// `OptTokens` both index under every token they carry — see `Ft`'s own
/// doc comment for why the oracle treats the two identically here;
/// anything else (`Epsilon`/`Unknown`, or a degenerate empty token list)
/// can't be bounded, so it's indexed as `FirstTok::Any` — tried on every
/// dispatch, exactly like the oracle's unconditional `leadingParsers`/
/// `trailingParsers` fallback list.
pub(crate) fn index_entries(p: &Prim) -> Vec<FirstTok> {
    match first_tokens(p) {
        Ft::Tokens(tks) | Ft::OptTokens(tks) if !tks.is_empty() => ft_dedup(tks),
        _ => vec![FirstTok::Any],
    }
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
        | Group(q) | WithPosition(q) | Many1Indent(q) | IncQuotDepth(q) | DecQuotDepth(q)
        | Many1Unbox(q) | WithoutAnonymousAntiquot(q) => walk_symbols(q, f),
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
        | DocCommentBody
        // `DynamicQuotBody` carries no `Prim::Symbol` of its own to
        // harvest here (it's an engine-special leaf, like
        // `UnknownTacticIdent`/`DocCommentBody` above, whose runtime
        // `expect_atom("|", ..)` call — see `dynamic_quot_body` in
        // parse.rs — checks the TABLE directly rather than going
        // through a `Prim::Symbol` node). This is harmless, not a gap:
        // `"|"` is already registered snapshot-wide by every `matchAlt`-
        // shaped production (`term_pragma.rs`'s `match_expr_alt`,
        // `term.rs`'s `match_alt`, `do_notation.rs`'s `doMatch`, …), so
        // by the time ANY `dynamicQuot` production is reachable the
        // token is already in the table.
        | DynamicQuotBody => {}
    }
}

/// M3b3 Task 8: derive the antiquot-splice-suffix TOKEN(s) a `SepBy`/
/// `SepBy1` production's separator implies, closing the silent-misparse
/// gap `builtin/mod.rs`'s own `",*"` comment documents — ORACLE
/// `sepByElemParser p sep := withAntiquotSpliceAndSuffix `sepBy p (symbol
/// (sep.trimAscii.copy ++ "*"))` (`Basic.lean:1895-1896`) applies
/// UNCONDITIONALLY to every `sepBy`/`sepBy1` combinator, not just the
/// hardcoded `sep = ","` case `builtin/mod.rs` registers by hand — this
/// walk generalizes that registration to ANY separator a same-file
/// `syntax`/`macro` declaration (`Overlay::register`) or an imported
/// production (`SnapshotBuilder::leading_prim`/`trailing_prim`/
/// `scoped_leading_prim`/`scoped_trailing_prim`) introduces.
///
/// Deliberately its OWN recursive walk rather than a `walk_symbols`
/// callback: `walk_symbols` already harvests `sep` itself as a bare
/// token (needed regardless of any suffix) every time it visits a
/// `SepBy`/`SepBy1`/`SepByIndent` node; folding suffix derivation into
/// the SAME callback would force every `walk_symbols` call site (in
/// particular the builtin snapshot's own `leading2`/`trailing2`, which
/// intentionally do NOT auto-register `"|*"`/`"▸*"` for `matchAlt`'s/
/// `anonymousCtor`'s own hardcoded `|`/`▸` separators — see that
/// comment's "don't force it" discipline) to gain suffix tokens it
/// never asked for.
///
/// M3b3 Task 9 adds the `SepByIndent` arm: ORACLE-PORT `sepByIndent`/
/// `sepBy1Indent` (`Extra.lean:202-208`) wrap their item in
/// `withAntiquotSpliceAndSuffix `sepBy p (symbol "*")` — note the FIXED
/// literal `"*"`, NOT `sep.trimAscii ++ "*"` like `sepByElemParser`
/// (`Basic.lean:1895-1896`) above. A `sepByIndent`-shaped production's
/// splice-suffix token is therefore always the bare `"*"`, independent
/// of its own `sep` field — confirmed directly from the toolchain
/// source (no oracle dump can observe this token in isolation; the
/// scope-splice form `$[$xs]*` a fixture DOES exercise
/// (`StxSepIndent.lean`) only proves `"*"` parses as a suffix, not that
/// it's `sep`-independent — that half of the claim rests on the source
/// reading alone, same "read the definition, don't just pattern-match
/// the dump" discipline `Prim::SepByIndent`'s own doc comment already
/// applies).
pub(crate) fn sepby_suffix_tokens(p: &Prim, out: &mut Vec<String>) {
    use Prim::*;
    match p {
        Seq(ps) | OrElse(ps) => {
            for q in ps {
                sepby_suffix_tokens(q, out);
            }
        }
        Node { body, .. } | TrailingNode { body, .. } => sepby_suffix_tokens(body, out),
        Optional(q) | Many(q) | Many1(q) | Atomic(q) | Lookahead(q) | NotFollowedBy(q)
        | Group(q) | WithPosition(q) | Many1Indent(q) | IncQuotDepth(q) | DecQuotDepth(q)
        | Many1Unbox(q) | WithoutAnonymousAntiquot(q) => sepby_suffix_tokens(q, out),
        WithForbidden(_tok, q) => sepby_suffix_tokens(q, out),
        WithoutForbidden(q) => sepby_suffix_tokens(q, out),
        SepBy { item, sep, .. } | SepBy1 { item, sep, .. } => {
            out.push(format!("{sep}*"));
            sepby_suffix_tokens(item, out);
        }
        SepByIndent { item, .. } => {
            out.push("*".to_string());
            sepby_suffix_tokens(item, out);
        }
        _ => {}
    }
}

#[cfg(test)]
mod ft_index_tests {
    use super::*;

    /// Task 11 item (a): `declaration` (`declModifiers`-optional lead)
    /// and `section` (`sectionHeader`-optional lead) must be indexed by
    /// their real mandatory keyword(s), not solely `FirstTok::Any` —
    /// this is the exact defect the brief calls out by name
    /// ("INCLUDING `declaration` and `section`"). Checked directly
    /// against the crate's own real builtin grammar (not a toy
    /// snapshot), reading `Category::leading`'s `pub(crate)` fields —
    /// the observable-behavior counterpart (`recover_command` actually
    /// resyncing on these keywords) is covered end-to-end by
    /// `oracle_golden.rs`'s
    /// `recover_command_resyncs_at_every_common_command_keyword`.
    #[test]
    fn declaration_and_section_are_indexed_by_their_mandatory_keyword_not_only_any() {
        let snap = crate::builtin::snapshot();
        let kinds = snap.kinds();
        let cmd = snap.categories.get("command").expect("command category");

        let leading_kind_names_for = |tok: &str| -> Vec<String> {
            cmd.leading
                .iter()
                .filter(|(f, _)| matches!(f, FirstTok::Sym(s) if s == tok))
                .map(|(_, idx)| match &cmd.leading_parsers[*idx] {
                    Prim::Node { kind, .. } => kinds.name(*kind).to_string(),
                    _ => "<unwrapped>".to_string(),
                })
                .collect()
        };

        let def_names = leading_kind_names_for("def");
        assert!(
            def_names.contains(&"Lean.Parser.Command.declaration".to_string()),
            "expected `declaration` indexed under Sym(\"def\"), got {def_names:?}"
        );
        let theorem_names = leading_kind_names_for("theorem");
        assert!(
            theorem_names.contains(&"Lean.Parser.Command.declaration".to_string()),
            "expected `declaration` indexed under Sym(\"theorem\"), got {theorem_names:?}"
        );
        let structure_names = leading_kind_names_for("structure");
        assert!(
            structure_names.contains(&"Lean.Parser.Command.declaration".to_string()),
            "expected `declaration` indexed under Sym(\"structure\"), got {structure_names:?}"
        );
        let section_names = leading_kind_names_for("section");
        assert!(
            section_names.contains(&"Lean.Parser.Command.section".to_string()),
            "expected `section` indexed under Sym(\"section\"), got {section_names:?}"
        );
        // `declaration`'s `declModifiers` optional prefix must ALSO
        // surface it under every modifier keyword (`private`, `@[`,
        // `/--`, …) — the whole point of the `OptTokens`/`seq` fix.
        for tok in ["private", "public", "@[", "/--", "protected", "unsafe"] {
            let names = leading_kind_names_for(tok);
            assert!(
                names.contains(&"Lean.Parser.Command.declaration".to_string()),
                "expected `declaration` indexed under Sym({tok:?}), got {names:?}"
            );
        }
        // Negative control: `declaration` must NOT be registered under
        // `FirstTok::Any` any more (the pre-fix state) — every entry
        // pointing at its `leading_parsers` index must be a real
        // `FirstTok::Sym`.
        let declaration_idx = cmd
            .leading_parsers
            .iter()
            .position(|p| matches!(p, Prim::Node { kind, .. } if kinds.name(*kind) == "Lean.Parser.Command.declaration"))
            .expect("declaration registered");
        let any_count_for_declaration = cmd
            .leading
            .iter()
            .filter(|(f, idx)| *idx == declaration_idx && matches!(f, FirstTok::Any))
            .count();
        assert_eq!(
            any_count_for_declaration, 0,
            "`declaration` must no longer be indexed under FirstTok::Any"
        );
    }
}

/// M3b2a Task 4: the three new seams — `builtin::builder()` (a
/// pre-registered `SnapshotBuilder` `leanr_grammar` can append to before
/// `finish()`) and `leading_prim`/`trailing_prim` (registering an
/// already-`Node`/`TrailingNode`-shaped `Prim`, as an interpreted
/// imported `ParserDescr` arrives).
#[cfg(test)]
mod builder_seam_tests {
    use super::*;

    #[test]
    fn leading_prim_registers_and_dispatches() {
        let mut b = crate::builtin::builder();
        let kind = b.kind("Test.imported");
        b.token("@@@");
        b.leading_prim(
            "term",
            Prim::Node {
                kind,
                prec: Some(LEAD_PREC),
                body: std::sync::Arc::new(Prim::Seq(vec![
                    Prim::Symbol("@@@".into()),
                    Prim::Category {
                        name: "term".into(),
                        rbp: MAX_PREC,
                    },
                ])),
            },
        );
        let snap = b.finish();
        let r = crate::parse_module("#check @@@1\n", &snap);
        assert!(r.errors.is_empty(), "{:?}", r.errors);
        assert_eq!(r.tree.text(), "#check @@@1\n");
        assert!(crate::canon::canon_jsonl(&r.tree).contains("Test.imported"));
    }

    #[test]
    fn builder_finish_equals_builtin_snapshot() {
        assert_eq!(
            crate::builtin::builder().finish().fingerprint(),
            crate::builtin::snapshot().fingerprint()
        );
    }

    /// M3b3 Task 5: `scoped_leading_prim` folds an imported `scoped`
    /// production PRESENT-but-INACTIVE — its atom does NOT enter the
    /// always-active token table (so it lexes as an ident until active),
    /// and its production only dispatches once its namespace is brought
    /// into force by `open`/`namespace`. Tests the snapshot mechanism in
    /// isolation from the olean decode (the `leanr_grammar` assemble path
    /// is pinned separately, against real oracle dumps).
    #[test]
    fn scoped_leading_prim_is_inactive_until_open_or_namespace() {
        let build = || {
            let mut b = crate::builtin::builder();
            let kind = b.kind("Foo.imported");
            b.scoped_leading_prim(
                "term",
                "Foo",
                Prim::Node {
                    kind,
                    prec: Some(LEAD_PREC),
                    body: std::sync::Arc::new(Prim::Seq(vec![
                        Prim::Symbol("⊘⊘".into()),
                        Prim::Category {
                            name: "term".into(),
                            rbp: MAX_PREC,
                        },
                    ])),
                },
            );
            b.finish()
        };
        let snap = build();
        // Tagged with its activation namespace, present in scoped storage.
        assert!(snap.scoped_namespaces().contains("Foo"));
        // Its atom is NOT in the always-active token table.
        assert!(!snap.tokens.contains("⊘⊘"));

        // Inactive: no `open Foo` in force → the scoped production never
        // dispatches, so the term after `#check` cannot consume `⊘⊘1`.
        let closed = crate::parse_module("#check ⊘⊘1\n", &snap);
        assert!(!closed.errors.is_empty(), "{:?}", closed.errors);

        // Active via `open Foo`.
        let opened = crate::parse_module("open Foo\n#check ⊘⊘1\n", &snap);
        assert!(opened.errors.is_empty(), "{:?}", opened.errors);
        assert!(crate::canon::canon_jsonl(&opened.tree).contains("Foo.imported"));

        // Active via `namespace Foo`, and DEACTIVATES again after `end`.
        let ns = crate::parse_module("namespace Foo\n#check ⊘⊘1\nend Foo\n#check ⊘⊘1\n", &snap);
        // The in-namespace use parses; the post-`end` use does not — so at
        // least one error is recorded, but the first `#check` still built a
        // `Foo.imported` node.
        assert!(
            crate::canon::canon_jsonl(&ns.tree).contains("Foo.imported"),
            "in-namespace use must activate"
        );
        assert!(
            !ns.errors.is_empty(),
            "post-`end Foo` use must deactivate and fail: {:?}",
            ns.errors
        );
    }

    /// M3b3 Task 8: `leading_prim` (the imported-production seam
    /// `leanr_grammar::assemble` folds a decoded `ParserDescr.sepBy`/
    /// `.sepBy1` through) must derive the SAME combined `"|*"`
    /// antiquot-splice-suffix token a same-file `Overlay::register`
    /// would for an identical `sepBy(.., "|")` shape — an imported
    /// module's own non-`,` separator gets the identical treatment, not
    /// just the hardcoded `sep = ","` builtin case.
    #[test]
    fn leading_prim_derives_sepby_suffix_token_for_imported_production() {
        let mut b = crate::builtin::builder();
        let kind = b.kind("Test.importedSepBy");
        b.token("wobalt");
        b.leading_prim(
            "term",
            Prim::Node {
                kind,
                prec: Some(MAX_PREC),
                body: std::sync::Arc::new(Prim::Seq(vec![
                    Prim::Symbol("wobalt".into()),
                    Prim::SepBy {
                        item: std::sync::Arc::new(Prim::Category {
                            name: "term".into(),
                            rbp: 0,
                        }),
                        sep: "|".into(),
                        allow_trailing: false,
                    },
                ])),
            },
        );
        let snap = b.finish();
        assert!(
            snap.tokens.contains("|*"),
            "expected the derived \"|*\" splice-suffix token in the always-active table"
        );
    }

    /// M3b3 Task 8: the scoped twin — `scoped_leading_prim`'s derived
    /// suffix token must land in `scoped_tokens` under the SAME
    /// namespace as the production itself, NOT the always-active table,
    /// so an inactive scoped `sepBy` production's `"|*"` doesn't leak
    /// into lexing before its namespace is opened (same discipline
    /// `scoped_leading_prim_is_inactive_until_open_or_namespace` already
    /// pins for the bare separator/atom case).
    #[test]
    fn scoped_leading_prim_scopes_the_sepby_suffix_token_to_its_namespace() {
        let mut b = crate::builtin::builder();
        let kind = b.kind("Foo.importedSepBy");
        b.scoped_leading_prim(
            "term",
            "Foo",
            Prim::Node {
                kind,
                prec: Some(MAX_PREC),
                body: std::sync::Arc::new(Prim::Seq(vec![
                    Prim::Symbol("gobalt".into()),
                    Prim::SepBy {
                        item: std::sync::Arc::new(Prim::Category {
                            name: "term".into(),
                            rbp: 0,
                        }),
                        sep: "|".into(),
                        allow_trailing: false,
                    },
                ])),
            },
        );
        let snap = b.finish();
        // Never in the always-active table.
        assert!(!snap.tokens.contains("|*"));
        // Present, tagged with the declaring namespace.
        assert!(snap
            .scoped_tokens
            .iter()
            .any(|(t, ns)| t == "|*" && ns == "Foo"));
    }

    /// M3b3 Task 5: a scoped entry participates in the fingerprint (a
    /// snapshot differing only in a scoped production/token/namespace must
    /// hash differently), while a scoped-FREE builder still finishes
    /// byte-identical to `builtin::snapshot()` (guarded by
    /// `builder_finish_equals_builtin_snapshot` above — this adds the
    /// "scoped changes it" direction).
    #[test]
    fn scoped_entries_change_the_fingerprint() {
        let base = crate::builtin::builder().finish().fingerprint();
        let with_scoped = {
            let mut b = crate::builtin::builder();
            let kind = b.kind("Foo.imported");
            b.scoped_leading_prim(
                "term",
                "Foo",
                Prim::Node {
                    kind,
                    prec: Some(LEAD_PREC),
                    body: std::sync::Arc::new(Prim::Symbol("⊘⊘".into())),
                },
            );
            b.finish().fingerprint()
        };
        assert_ne!(base, with_scoped, "a scoped entry must change the fingerprint");
    }
}
