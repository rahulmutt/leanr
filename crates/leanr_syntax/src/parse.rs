//! The Prim interpreter (spec §Architecture / parse). One mutable state
//! (`Ps`) over the event list; speculation = truncate-to-savepoint;
//! Pratt trailing wrap = insert Start at the lhs event index (Task 6).
//! Failure carries no data — the state records the furthest failure
//! position + expected set for diagnostics (Lean errorMsg merging).
//!
//! `Ps` holds `&GrammarSnapshot` (Task 6): the single explicit,
//! hash-fingerprintable parser-state value (spec §Architecture — the
//! M5 query-firewall seam). Categories/Pratt dispatch (`category`),
//! position/indentation checks, and the precedence gates all read
//! through it; nothing here is global.

use std::sync::Arc;

use crate::grammar::{Category, FirstTok, GrammarSnapshot, Prim};
use crate::kind::{
    KindInterner, SyntaxKind, KIND_ATOM, KIND_ERROR, KIND_ERROR_TOKEN, KIND_GROUP, KIND_IDENT,
    KIND_NULL,
};
use crate::lex::{next_token, Token, TokenKind, TokenTable};
use crate::tree::{build_tree, Event, SyntaxTree};

/// The result of parsing one module (spec §Oracle harness / Task 7's
/// vertical slice — the caller `leanr_syntax::parse_module` re-exports
/// from `lib.rs`): a lossless tree, always (untrusted-input totality —
/// a bad parse still yields a tree with `KIND_ERROR` nodes) plus
/// whatever diagnostics were recorded along the way.
#[derive(Debug)]
pub struct ParseResult {
    pub tree: SyntaxTree,
    pub errors: Vec<ParseError>,
}

/// Parse one module: header, then commands to EOF. Never panics; a
/// command that fails to parse becomes a `KIND_ERROR` node and parsing
/// resumes at the next plausible command start (`recover_command`;
/// Task 11 hardens the recovery heuristic further). ORACLE-PORT
/// `Lean/Parser/Module.lean` `parseHeader`/`parseCommand`/`mkEOI`: the
/// trailing `Lean.Parser.Command.eoi` node (a single empty atom at EOF)
/// mirrors what a real oracle dump of this loop always emits last —
/// confirmed against a fresh `dump_syntax.lean` run over
/// `tests/fixtures/syntax/Micro.lean` (Task 7), not assumed from source.
pub fn parse_module(src: &str, snap: &GrammarSnapshot) -> ParseResult {
    let kinds = snap.kinds();
    let mut ps = Ps::new(src, snap);
    let module = kinds
        .lookup("module")
        .expect("interned by builtin::snapshot");
    ps.start(module);

    // Header (always present; all-optional parts ⇒ cannot fail).
    let header = snap
        .header_prim()
        .expect("builtin::snapshot() always sets a header (PF2)");
    let _ = ps.run(&header);

    // Command loop.
    loop {
        let (t, _at) = ps.peek_significant();
        if t.kind == TokenKind::Eof {
            break;
        }
        let sp = ps.save();
        match ps.run(&Prim::Category {
            name: "command".into(),
            rbp: 0,
        }) {
            Ok(()) => {}
            Err(_) => {
                ps.restore(&sp);
                ps.recover_command();
            }
        }
    }
    // Trailing eoi node: a single empty atom at EOF, mirroring
    // `mkEOI`'s `mkNode ``Command.eoi #[atom]`` where `atom` is a
    // zero-width `Syntax.atom` at the final position. By the time the
    // loop above breaks, `peek_significant` has already drained any
    // trailing trivia up to true EOF as a side effect of its own
    // `Eof`-detecting peek, so `ps.pos` here IS that position already
    // — no extra peek needed.
    let eoi = kinds
        .lookup("Lean.Parser.Command.eoi")
        .expect("interned by builtin::snapshot");
    ps.start(eoi);
    ps.emit_token(KIND_ATOM, 0);
    ps.finish();

    ps.finish(); // module
    let (tree, errors) = ps.finish_into_tree();
    ParseResult { tree, errors }
}

impl<'a> Ps<'a> {
    /// Minimal recovery: emit an ERROR node, skip tokens until the next
    /// token that could START a command (per the command category's
    /// dispatch index) or EOF; always consume ≥ 1 token. Also surfaces
    /// the furthest-failure diagnostic (E0301).
    ///
    /// PF3 resolution (task-7-brief): every non-Ident, non-`ErrorTok`
    /// token skipped here becomes `KIND_ATOM`; `TokenKind::ErrorTok`
    /// maps to `KIND_ERROR_TOKEN` specifically — that kind (Task 1) is
    /// otherwise unreachable, and canon.rs already special-cases it as
    /// never-oracle-compared.
    pub(crate) fn recover_command(&mut self) {
        let (pos, expected) = (self.furthest_pos, self.furthest_expected.clone());
        self.errors.push(ParseError {
            code: "E0301",
            span: (pos as u32, pos as u32),
            msg: format!("unexpected input; expected one of: {}", expected.join(", ")),
        });
        self.start(KIND_ERROR);
        let mut first = true;
        loop {
            let (t, at) = self.peek_significant();
            if t.kind == TokenKind::Eof {
                break;
            }
            let text = &self.src[at..at + t.len as usize];
            if !first && self.starts_command(text, t.kind) {
                break;
            }
            first = false;
            let kind = match t.kind {
                TokenKind::Ident => KIND_IDENT,
                TokenKind::ErrorTok => KIND_ERROR_TOKEN,
                _ => KIND_ATOM,
            };
            self.bump(t, kind);
        }
        self.finish();
    }

    /// Conservative "could this token start a command" test: does the
    /// "command" category's leading dispatch have a `FirstTok::Sym`
    /// entry matching this exact text? (No `Any`-indexed fallback here
    /// — recovery only needs to be conservative, not complete; a false
    /// negative just means one more token gets swept into the error
    /// node, which is still a lossless, terminating recovery.)
    fn starts_command(&self, text: &str, kind: TokenKind) -> bool {
        if kind != TokenKind::Atom {
            return false;
        }
        let Some(cat) = self.snap_category("command") else {
            return false;
        };
        cat.leading
            .iter()
            .any(|(f, _)| matches!(f, FirstTok::Sym(s) if s == text))
    }
}

/// Depth cap on input-driven `Category` recursion (nested parens and
/// the like — adversarial input can nest these arbitrarily, and
/// `category` recurses through `Ps::run` for every level). Not an
/// oracle port — Lean's own `maxRecDepth` (`CoreM.lean`, default 1000)
/// governs elaborator/tactic recursion on a native stack with its own
/// (`stacker`-grown) headroom; `leanr_syntax` cannot depend on
/// `leanr_kernel`'s `RecGuard` (no workspace deps allowed here) or add
/// `stacker` itself (no new external deps), so this is a minimal,
/// from-scratch equivalent — a plain counter, no stack-growing trick,
/// which means the cap must itself be low enough to never overflow the
/// HOST stack, not just "low enough to be a sane grammar depth".
/// Empirically bisected on this build (debug/unoptimized, the
/// `cargo test`-default profile — see `mise run test`): a
/// `libtest`-spawned test thread's default stack overflows somewhere
/// between 300 and 320 levels of this crate's actual `category()`
/// recursion (`adversarial_nesting_terminates_without_overflow`
/// pins this); 128 leaves better than 2x headroom under that measured
/// floor.
const MAX_CATEGORY_DEPTH: u32 = 128;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub code: &'static str,
    /// Byte span the error points at.
    pub span: (u32, u32),
    pub msg: String,
}

/// Parse failure marker; all context lives in `Ps` (furthest/expected).
#[derive(Debug)]
pub struct Fail;
pub type PResult = Result<(), Fail>;

// This whole apparatus is exercised today only by the toy-grammar tests
// below — Task 5 has no *production* caller yet (that's `parse_module`,
// Task 7, over a real `GrammarSnapshot`, Task 6). `cfg(test)` strips
// `mod tests` from the plain (non-test) build, which would otherwise
// make every item here look unreachable to `dead_code` — hence the
// `cfg_attr` rather than a real bug to silence.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) struct Ps<'a> {
    src: &'a str,
    pub(crate) pos: usize,
    snap: &'a GrammarSnapshot,
    /// Cloned once at construction (`Arc` bump) so every lookup below
    /// (`lit`/`field_idx`, tree-building) reads through a plain owned
    /// field rather than re-deriving from `snap` each time.
    kinds: Arc<KindInterner>,
    events: Vec<Event>,
    pub(crate) errors: Vec<ParseError>,
    furthest_pos: usize,
    furthest_expected: Vec<String>,
    /// Current right-binding power: `Category` sets it on recursion,
    /// `Node`'s `prec` gate reads it.
    prec: u32,
    /// Precedence of the last completed leading/trailing node.
    lhs_prec: u32,
    /// `withPosition` stack: saved (line, col) of a position marker.
    pos_stack: Vec<(u32, u32)>,
    /// Byte offset of each line start (for column computation).
    line_starts: Vec<usize>,
    /// Input-driven `Category` recursion depth — see
    /// `MAX_CATEGORY_DEPTH`.
    cat_depth: u32,
}

#[cfg_attr(not(test), allow(dead_code))]
pub(crate) struct Savepoint {
    pos: usize,
    events: usize,
    errors: usize,
    lhs_prec: u32,
}

/// A `longest_match` winner: which candidate won, the events/errors it
/// produced (relative to the shared savepoint), where it left `pos`,
/// and its resulting `lhs_prec`. A named struct (not a tuple) purely
/// to keep `longest_match`'s signature under clippy's type-complexity
/// threshold.
#[cfg_attr(not(test), allow(dead_code))]
struct MatchWinner {
    idx: usize,
    events: Vec<Event>,
    errors: Vec<ParseError>,
    end: usize,
    lhs_prec: u32,
}

#[cfg_attr(not(test), allow(dead_code))]
impl<'a> Ps<'a> {
    pub(crate) fn new(src: &'a str, snap: &'a GrammarSnapshot) -> Self {
        let mut line_starts = vec![0];
        for (i, b) in src.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(i + 1);
            }
        }
        let kinds = snap.kinds();
        Ps {
            src,
            pos: 0,
            snap,
            kinds,
            events: Vec::new(),
            errors: Vec::new(),
            furthest_pos: 0,
            furthest_expected: Vec::new(),
            prec: 0,
            lhs_prec: 0,
            pos_stack: Vec::new(),
            line_starts,
            cat_depth: 0,
        }
    }

    fn table(&self) -> &TokenTable {
        &self.snap.tokens
    }

    fn snap_category(&self, name: &str) -> Option<&'a Category> {
        self.snap.categories.get(name)
    }

    // ---- events ----------------------------------------------------
    pub(crate) fn start(&mut self, kind: SyntaxKind) {
        self.events.push(Event::Start(kind));
    }
    pub(crate) fn finish(&mut self) {
        self.events.push(Event::Finish);
    }
    pub(crate) fn save(&self) -> Savepoint {
        Savepoint {
            pos: self.pos,
            events: self.events.len(),
            errors: self.errors.len(),
            lhs_prec: self.lhs_prec,
        }
    }
    pub(crate) fn restore(&mut self, sp: &Savepoint) {
        self.pos = sp.pos;
        self.events.truncate(sp.events);
        self.errors.truncate(sp.errors);
        self.lhs_prec = sp.lhs_prec;
    }
    fn consumed_since(&self, sp: &Savepoint) -> bool {
        self.pos > sp.pos
    }

    // ---- tokens ----------------------------------------------------
    /// Emit trivia events up to the next significant token; return it
    /// (without consuming) plus its start offset.
    pub(crate) fn peek_significant(&mut self) -> (Token, usize) {
        loop {
            let (t, err) = next_token(self.src, self.pos, self.table());
            let trivia = matches!(
                t.kind,
                TokenKind::Whitespace | TokenKind::LineComment | TokenKind::BlockComment
            );
            if !trivia {
                return (t, self.pos);
            }
            if let Some(e) = err {
                self.errors.push(ParseError {
                    code: e.code,
                    span: (self.pos as u32, (self.pos + t.len as usize) as u32),
                    msg: e.msg,
                });
            }
            self.emit_token(trivia_kind(t.kind), t.len);
        }
    }

    /// Peek the next significant token as a candidate for a single-token
    /// leaf match; returns the token, its start offset, and a savepoint
    /// captured BEFORE this peek scanned any trivia. On a mismatch, the
    /// caller restores to that savepoint before failing, so leading
    /// trivia this peek had to skip never counts as "consumption" for
    /// `OrElse`/`Optional`/`Many` backtracking decisions.
    ///
    /// ORACLE-PORT `Lean/Parser/Types.lean` `mkUnexpectedTokenErrors`:
    /// on a token mismatch it resets `s.pos` to the PRE-token position
    /// (`s.setPos iniPos`), discarding whatever `tokenFn` advanced through
    /// while locating the (wrong) token — this is that reset. Without it,
    /// any failing alternative preceded by whitespace/comments would
    /// look like it "consumed" input and `OrElse` would wrongly refuse
    /// to try the next one — i.e. almost every alternative in real
    /// source, since whitespace before a token is the common case.
    fn peek_for_match(&mut self) -> (Token, usize, Savepoint) {
        let sp = self.save();
        let (t, at) = self.peek_significant();
        (t, at, sp)
    }

    fn emit_token(&mut self, kind: SyntaxKind, len: u32) {
        self.events.push(Event::Token {
            kind,
            offset: self.pos as u32,
            len,
        });
        self.pos += len as usize;
    }

    /// Consume the peeked significant token as leaf `kind`.
    fn bump(&mut self, t: Token, kind: SyntaxKind) {
        if let (_, Some(e)) = next_token(self.src, self.pos, self.table()) {
            self.errors.push(ParseError {
                code: e.code,
                span: (self.pos as u32, (self.pos + t.len as usize) as u32),
                msg: e.msg,
            });
        }
        self.emit_token(kind, t.len);
    }

    fn fail_expecting(&mut self, what: &str, at: usize) -> Fail {
        if at > self.furthest_pos {
            self.furthest_pos = at;
            self.furthest_expected.clear();
        }
        if at == self.furthest_pos {
            let w = what.to_string();
            if !self.furthest_expected.contains(&w) {
                self.furthest_expected.push(w);
            }
        }
        Fail
    }

    /// Render the running furthest-failure tally as a stable-coded
    /// diagnostic (E0301 — unexpected token / expected-one-of). Callers
    /// push this exactly once per *unresolved* top-level failure: a
    /// failure some enclosing `OrElse`/`Atomic` went on to recover from
    /// (by succeeding via a different alternative) must NOT also record
    /// one. ORACLE-PORT: Lean's `errorMsg` merges every alternative's
    /// expected set at the furthest position reached; this is that merge
    /// rendered as our `ParseError`. Task 7/11's `recover_command` is the
    /// first real (non-test) caller.
    pub(crate) fn push_furthest_error(&mut self) {
        let msg = if self.furthest_expected.is_empty() {
            "unexpected input".to_string()
        } else {
            format!(
                "unexpected input; expected one of: {}",
                self.furthest_expected.join(", ")
            )
        };
        self.errors.push(ParseError {
            code: "E0301",
            span: (self.furthest_pos as u32, self.furthest_pos as u32),
            msg,
        });
    }

    // ---- the interpreter --------------------------------------------
    pub(crate) fn run(&mut self, p: &Prim) -> PResult {
        match p {
            Prim::Seq(ps) => {
                for q in ps {
                    self.run(q)?;
                }
                Ok(())
            }
            Prim::Node { kind, prec, body } => {
                if let Some(np) = prec {
                    if *np < self.prec {
                        let at = self.pos;
                        return Err(self.fail_expecting("<prec>", at));
                    }
                }
                self.start(*kind);
                let r = self.run(body);
                // Node ALWAYS finishes, success or failure — the
                // subtree stays balanced either way. An enclosing
                // `OrElse`/`Optional`/etc.'s `restore()` is what
                // discards it if a different alternative is chosen.
                self.finish();
                if r.is_ok() {
                    self.lhs_prec = prec.unwrap_or(0);
                }
                r
            }
            Prim::Symbol(s) => self.expect_atom(s, false),
            Prim::NonReservedSymbol(s) => self.expect_atom(s, true),
            Prim::Ident => {
                let (t, at, sp) = self.peek_for_match();
                if t.kind == TokenKind::Ident {
                    self.bump(t, KIND_IDENT);
                    Ok(())
                } else {
                    self.restore(&sp);
                    Err(self.fail_expecting("identifier", at))
                }
            }
            Prim::NumLit => self.lit(TokenKind::Num, "num"),
            Prim::ScientificLit => self.lit(TokenKind::Scientific, "scientific"),
            Prim::StrLit => self.lit(TokenKind::Str, "str"),
            Prim::CharLit => self.lit(TokenKind::Char, "char"),
            Prim::NameLit => self.lit(TokenKind::NameLit, "name"),
            Prim::FieldIdx => self.field_idx(),
            Prim::Optional(q) => {
                let sp = self.save();
                self.start(KIND_NULL);
                match self.run(q) {
                    Ok(()) => {
                        self.finish();
                        Ok(())
                    }
                    Err(f) if self.consumed_since(&sp) => {
                        // ORACLE-PORT `optionalFn`: `s.mkNode nullKind
                        // iniSz` wraps the result UNCONDITIONALLY,
                        // success or failure — a consuming failure must
                        // still close this `null` node, or the dangling
                        // `Start` corrupts the event stream.
                        self.finish();
                        Err(f)
                    }
                    Err(_) => {
                        self.restore(&sp);
                        self.start(KIND_NULL);
                        self.finish();
                        Ok(())
                    }
                }
            }
            Prim::Many(q) => self.many_impl(q, 0),
            Prim::Many1(q) => self.many_impl(q, 1),
            Prim::SepBy {
                item,
                sep,
                allow_trailing,
            } => self.sep_by_impl(item, sep, *allow_trailing, 0),
            Prim::SepBy1 {
                item,
                sep,
                allow_trailing,
            } => self.sep_by_impl(item, sep, *allow_trailing, 1),
            Prim::OrElse(alts) => {
                for alt in alts {
                    let sp = self.save();
                    match self.run(alt) {
                        Ok(()) => return Ok(()),
                        Err(f) if self.consumed_since(&sp) => return Err(f),
                        Err(_) => self.restore(&sp),
                    }
                }
                let at = self.pos;
                Err(self.fail_expecting("<alternative>", at))
            }
            Prim::Atomic(q) => {
                let sp = self.save();
                self.run(q).inspect_err(|_| self.restore(&sp))
            }
            Prim::Lookahead(q) => {
                let sp = self.save();
                let r = self.run(q);
                self.restore(&sp);
                r
            }
            Prim::NotFollowedBy(q) => {
                let sp = self.save();
                let r = self.run(q);
                self.restore(&sp);
                match r {
                    Ok(()) => {
                        let at = self.pos;
                        Err(self.fail_expecting("<not-followed-by>", at))
                    }
                    Err(_) => Ok(()),
                }
            }
            Prim::Group(q) => {
                self.start(KIND_GROUP);
                let r = self.run(q);
                self.finish();
                r
            }
            Prim::EmitMissing => {
                self.events.push(Event::Missing);
                Ok(())
            }
            Prim::EmitEmptyIdent => {
                // ORACLE-PORT `hygieneInfoFn`: always succeeds, emitting
                // a zero-width `ident` at the CURRENT position — no
                // `peek_significant` call, so no trivia is skipped
                // first (see the `Prim::EmitEmptyIdent` doc comment).
                self.events.push(Event::Token {
                    kind: KIND_IDENT,
                    offset: self.pos as u32,
                    len: 0,
                });
                Ok(())
            }
            Prim::RawChar(c) => {
                // ORACLE-PORT `rawCh`: reads exactly one raw source
                // character WITHOUT going through `next_token` (see the
                // `Prim::RawChar` doc comment) — never skips trivia,
                // never consults the token table.
                let at = self.pos;
                match self.src[at..].chars().next() {
                    Some(got) if got == *c => {
                        self.emit_token(KIND_ATOM, got.len_utf8() as u32);
                        Ok(())
                    }
                    _ => Err(self.fail_expecting(&format!("'{c}'"), at)),
                }
            }
            Prim::CheckPrec(n) => {
                // ORACLE-PORT `checkPrecFn` (Basic.lean): succeeds iff
                // `c.prec <= prec` — i.e. the surrounding right-binding
                // power must not exceed this checkpoint's threshold.
                if self.prec <= *n {
                    Ok(())
                } else {
                    let at = self.pos;
                    Err(self.fail_expecting("<prec>", at))
                }
            }
            Prim::CheckLhsPrec(n) => {
                // ORACLE-PORT `checkLhsPrecFn`: succeeds iff
                // `s.lhsPrec >= prec`.
                if self.lhs_prec >= *n {
                    Ok(())
                } else {
                    let at = self.pos;
                    Err(self.fail_expecting("<lhs-prec>", at))
                }
            }
            Prim::WithPosition(q) => {
                // ORACLE-PORT `withPosition` (Basic.lean): save the
                // CURRENT position (before any trivia this call's body
                // might skip is consumed) as the position marker for
                // nested `checkCol*`/`checkLineEq`, restoring the
                // previous marker (by popping) on the way out —
                // success or failure alike, since it's a pure scoping
                // combinator with no bearing on `q`'s own result.
                let (_, at) = self.peek_significant();
                let lc = self.line_col(at);
                self.pos_stack.push(lc);
                let r = self.run(q);
                self.pos_stack.pop();
                r
            }
            Prim::CheckColGt => self.check_col(|cur, saved| cur.1 > saved.1),
            Prim::CheckColGe => self.check_col(|cur, saved| cur.1 >= saved.1),
            Prim::CheckColEq => self.check_col(|cur, saved| cur.1 == saved.1),
            Prim::CheckLineEq => self.check_col(|cur, saved| cur.0 == saved.0),
            Prim::CheckWsBefore => {
                // Same trivia-consumption-on-failure hazard as
                // `check_col` (see there): `had_ws_before_current`'s
                // own peek can advance `self.pos` even when this check
                // ultimately fails, so a failing branch must restore.
                let sp = self.save();
                if self.had_ws_before_current() {
                    Ok(())
                } else {
                    let at = self.pos;
                    self.restore(&sp);
                    Err(self.fail_expecting("<whitespace>", at))
                }
            }
            Prim::CheckNoWsBefore => {
                let sp = self.save();
                if self.had_ws_before_current() {
                    let at = self.pos;
                    self.restore(&sp);
                    Err(self.fail_expecting("<no whitespace>", at))
                } else {
                    Ok(())
                }
            }
            Prim::Many1Indent(q) => {
                // ORACLE-PORT `Extra.lean` `many1Indent`: `withPosition
                // $ many1 (checkColGe "irrelevant" >> p)`.
                let expanded =
                    Prim::WithPosition(Arc::new(Prim::Many1(Arc::new(Prim::Seq(vec![
                        Prim::CheckColGe,
                        (**q).clone(),
                    ])))));
                self.run(&expanded)
            }
            Prim::SepByIndentSemicolon(q) => self.sep_by_indent(q),
            Prim::Category { name, rbp } => self.category(name, *rbp),
            Prim::TrailingNode { .. } => {
                // Only the category trailing loop may run these (it
                // owns the lhs wrap: it splices in the already-parsed
                // left-hand side's `Start`, retroactively, once this
                // candidate wins the trailing longest-match). A
                // `TrailingNode` reached any other way is a
                // grammar-construction bug, not a parse failure.
                unreachable!("TrailingNode outside a category trailing loop")
            }
        }
    }

    fn expect_atom(&mut self, s: &str, allow_ident: bool) -> PResult {
        let (t, at, sp) = self.peek_for_match();
        let text = &self.src[at..at + t.len as usize];
        let ok = match t.kind {
            TokenKind::Atom => text == s,
            TokenKind::Ident if allow_ident => text == s,
            _ => false,
        };
        if ok {
            self.bump(t, KIND_ATOM);
            Ok(())
        } else {
            self.restore(&sp);
            Err(self.fail_expecting(&format!("'{s}'"), at))
        }
    }

    fn lit(&mut self, want: TokenKind, kind_name: &str) -> PResult {
        let (t, at, sp) = self.peek_for_match();
        if t.kind == want {
            let kind = self
                .kinds
                .lookup(kind_name)
                .expect("literal kinds pre-interned by SnapshotBuilder");
            self.start(kind);
            self.bump(t, KIND_ATOM);
            self.finish();
            Ok(())
        } else {
            self.restore(&sp);
            Err(self.fail_expecting(kind_name, at))
        }
    }

    fn field_idx(&mut self) -> PResult {
        // Raw digits immediately after '.': the LEXER would produce a
        // Num (or Scientific for `x.1.2`!) — so FieldIdx lexes directly:
        // digits only, then wraps in "fieldIdx". ORACLE-PORT fieldIdxFn.
        // No leading trivia is possible here (a field-index always
        // follows an already-consumed `.` with nothing between), so
        // there's nothing to roll back on failure.
        let at = self.pos;
        let digits = self.src[at..]
            .bytes()
            .take_while(|b| b.is_ascii_digit())
            .count();
        if digits == 0 {
            return Err(self.fail_expecting("field index", at));
        }
        let kind = self.kinds.lookup("fieldIdx").expect("pre-interned");
        self.start(kind);
        self.emit_token(KIND_ATOM, digits as u32);
        self.finish();
        Ok(())
    }

    fn many_impl(&mut self, q: &Prim, min: usize) -> PResult {
        self.start(KIND_NULL);
        let mut n = 0usize;
        let result: PResult = loop {
            let sp = self.save();
            match self.run(q) {
                Ok(()) => {
                    if !self.consumed_since(&sp) {
                        // ORACLE-PORT `manyAux`: a zero-width successful
                        // item, repeated, can never terminate on its
                        // own — flagged exactly as the oracle does
                        // ("parser did not consume anything"), not
                        // looped forever. EXCEPT: `many1`'s (`min >= 1`)
                        // mandatory FIRST item is exempt — `many1Fn =
                        // andthenFn p (manyAux p)` runs that one
                        // unconditionally before `manyAux`'s own
                        // (unexempted) loop even starts, which is
                        // exactly the "at least one, possibly empty"
                        // idiom `many1(optional(...))` relies on. This
                        // does NOT short-circuit: the loop genuinely
                        // tries again (matching `manyAux`'s own
                        // independent re-invocation of `p`) — since `q`
                        // is deterministic, a second zero-width success
                        // is inevitable and THAT one hits the
                        // non-exempt branch below and errors, exactly
                        // as the oracle's "second" `p` call does.
                        if n == 0 && min >= 1 {
                            n = 1;
                            continue;
                        }
                        let at = self.pos;
                        break Err(self.fail_expecting("<many: zero-width item>", at));
                    }
                    n += 1;
                }
                Err(f) if self.consumed_since(&sp) => break Err(f),
                Err(_) => {
                    self.restore(&sp);
                    break Ok(());
                }
            }
        };
        // The `null` node is ALWAYS finished, success or failure —
        // ORACLE-PORT `manyFn`/`many1Fn`: `s.mkNode nullKind iniSz` runs
        // unconditionally over whatever the loop left behind. A
        // consuming failure mid-loop must still close this node, or the
        // dangling `Start` corrupts the event stream irrecoverably.
        self.finish();
        result?;
        if n < min {
            let at = self.pos;
            return Err(self.fail_expecting("<many1 item>", at));
        }
        Ok(())
    }

    fn sep_by_impl(&mut self, item: &Prim, sep: &str, allow_trailing: bool, min: usize) -> PResult {
        self.start(KIND_NULL);
        let mut n = 0usize;
        let mut after_sep = false;
        // No zero-width-item guard is needed here (unlike `many_impl`):
        // `sep` is always a fixed atom (`expect_atom`), and the lexer
        // guarantees a token match can never be zero-width (`next_token`
        // always advances ≥ 1 byte except at Eof) — so continuing this
        // loop after a zero-width `item` still requires `sep` to make
        // real progress, and a finite source can only do that finitely
        // often.
        let result: PResult = 'outer: loop {
            let sp = self.save();
            match self.run(item) {
                Ok(()) => n += 1,
                Err(f) if self.consumed_since(&sp) => break 'outer Err(f),
                Err(f) => {
                    self.restore(&sp);
                    if after_sep && !allow_trailing {
                        // `a, ` with no trailing separator allowed: the
                        // already-consumed separator makes this a real
                        // failure, not a clean end-of-list.
                        break 'outer Err(f);
                    }
                    break 'outer Ok(());
                }
            }
            let sp = self.save();
            match self.expect_atom(sep, false) {
                Ok(()) => after_sep = true,
                Err(_) => {
                    self.restore(&sp);
                    break 'outer Ok(());
                }
            }
        };
        // Same "always finish" requirement as `many_impl` — see there.
        self.finish();
        result?;
        if n < min {
            let at = self.pos;
            return Err(self.fail_expecting("<sepBy1 item>", at));
        }
        Ok(())
    }

    /// Sequence of `p` optionally separated by `;`, indentation-scoped
    /// (Lean tactic/do-block sequencing: `by skip; skip` or one `skip`
    /// per line, but not `by skip skip` on one line). ORACLE-PORT
    /// `Term/Basic.lean` `sepByIndentSemicolon` = `sepByIndent p "; "
    /// (allowTrailingSep := true)`, and `sepByIndent` itself
    /// (`Extra.lean`): `withPosition $ sepBy (checkColGe >> p) sep
    /// (psep <|> checkColEq >> checkLinebreakBefore >> pushNone)
    /// allowTrailingSep`. Each item must be at or past the marker's
    /// column; between items, EITHER an explicit `;` is consumed, OR —
    /// with no token at all — the next item starts on a new line at
    /// EXACTLY the marker's column (no semicolon needed when items are
    /// already visually separated by indentation; required when two
    /// share a line).
    fn sep_by_indent(&mut self, item: &Prim) -> PResult {
        let (_, at) = self.peek_significant();
        let lc = self.line_col(at);
        self.pos_stack.push(lc);
        self.start(KIND_NULL);
        let mut after_sep = false;
        let result: PResult = 'outer: loop {
            let sp = self.save();
            if self.check_col(|cur, saved| cur.1 >= saved.1).is_err() {
                self.restore(&sp);
                break 'outer Ok(());
            }
            match self.run(item) {
                Ok(()) => {}
                Err(f) if self.consumed_since(&sp) => break 'outer Err(f),
                Err(f) => {
                    self.restore(&sp);
                    if after_sep {
                        // allowTrailingSep := true — a trailing `;`
                        // (or an implicit newline-separator) with
                        // nothing following is a clean end, not this
                        // failure.
                        break 'outer Ok(());
                    }
                    break 'outer Err(f);
                }
            }
            let before_sep = self.pos;
            let sep_sp = self.save();
            match self.expect_atom(";", false) {
                Ok(()) => {
                    after_sep = true;
                    continue 'outer;
                }
                Err(_) => self.restore(&sep_sp),
            }
            // Implicit separator: next token at exactly the marker's
            // column AND a linebreak occurred since the last item.
            let coleq_sp = self.save();
            let coleq = self.check_col(|cur, saved| cur.1 == saved.1).is_ok();
            self.restore(&coleq_sp);
            if coleq {
                let (_, next_at) = self.peek_significant();
                if self.src[before_sep..next_at].contains('\n') {
                    after_sep = true;
                    continue 'outer;
                }
            }
            break 'outer Ok(());
        };
        // Same "always finish" requirement as `many_impl`/`sep_by_impl`
        // — a consuming failure mid-loop must still close this `null`
        // node, or the dangling `Start` corrupts the event stream.
        self.finish();
        self.pos_stack.pop();
        result
    }

    /// Character (codepoint) offset from `at`'s line start — ORACLE-
    /// PORT `Lean/Data/Position.lean` `FileMap.toPosition`'s `toColumn`:
    /// it walks the source one `Char` at a time (`i.next str`), i.e.
    /// codepoints, not bytes or UTF-16 units — verified in the pin.
    fn line_col(&self, at: usize) -> (u32, u32) {
        let line = self
            .line_starts
            .partition_point(|&s| s <= at)
            .saturating_sub(1);
        let col = self.src[self.line_starts[line]..at].chars().count();
        (line as u32, col as u32)
    }

    /// Shared body for `CheckColGt`/`CheckColGe`/`CheckColEq`/
    /// `CheckLineEq`: compare the upcoming token's (line, col) against
    /// the innermost `withPosition` marker. ORACLE-PORT `checkColGtFn`
    /// et al. (Basic.lean): with no marker active (`c.savedPos? =
    /// none`), the check is unconstrained — always succeeds.
    fn check_col(&mut self, ok: impl Fn((u32, u32), (u32, u32)) -> bool) -> PResult {
        // `peek_significant` skips trivia as a side effect (emitting
        // trivia events, advancing `self.pos`) regardless of whether
        // the column check that follows passes or fails. On failure
        // that side effect MUST be undone: a real bug found while
        // implementing this against the oracle (`checkColGtFn` et al.
        // read `s.pos` directly, with no trivia-skipping of their own —
        // they're pure zero-width checks) — without the restore here,
        // an indentation check that stops a `many1Indent`-style loop
        // (e.g. the next line dedents below the marker) would still
        // have consumed the intervening newline/whitespace, making the
        // enclosing `many_impl` see a "consuming failure" and abort
        // with an error instead of cleanly ending the loop.
        let sp = self.save();
        let (_, at) = self.peek_significant();
        let cur = self.line_col(at);
        let Some(&saved) = self.pos_stack.last() else {
            return Ok(());
        };
        if ok(cur, saved) {
            Ok(())
        } else {
            self.restore(&sp);
            Err(self.fail_expecting("<indentation>", at))
        }
    }

    /// ORACLE-PORT `checkTailWs`/`checkTailNoWs` (Basic.lean): whether
    /// the previously-parsed token has non-empty trailing trivia
    /// before the next significant token. Our event stream has no
    /// "trailing trivia" field on tokens (all trivia is its own flat
    /// event) so this is reconstructed two ways, covering both call
    /// patterns:
    /// - a peek not yet performed here advances `self.pos` past any
    ///   trivia when it scans it (`at > before`);
    /// - a peek already performed by an earlier combinator (e.g. the
    ///   `bump` that consumed the previous token) already did that
    ///   scan, so `self.pos == at` on entry — the trailing event is
    ///   then the tell.
    fn had_ws_before_current(&mut self) -> bool {
        let before = self.pos;
        let (_, at) = self.peek_significant();
        if at > before {
            return true;
        }
        // Nothing left for THIS call to skip — the previous combinator
        // already scanned past any trivia (e.g. the `bump` that
        // consumed the token before us, or an earlier
        // `peek_significant`). Whether that happened depends on
        // finding the most recent REAL token event, skipping over
        // zero-width structural noise (`Start`/`Finish`/`Missing`) —
        // Task 8 review fix: the previous version checked ONLY
        // `self.events.last()`, which broke the instant ANY wrapper
        // (`Optional`/`Many`/`Node`'s own `Start(..)`) sat between the
        // trivia token and this check — e.g. `Term.app`'s `many1
        // (checkWsBefore >> ..)`: `many_impl` pushes `Start(null)`
        // BEFORE running its body's first `CheckWsBefore`, so
        // `events.last()` was always that `Start`, never the
        // whitespace token right before it — `had_ws_before_current`
        // silently returned `false` for EVERY argument, breaking
        // application entirely. Skipping structural events to find the
        // last real token fixes this without changing behavior for the
        // (already-correct) no-wrapper case.
        self.events
            .iter()
            .rev()
            .find_map(|e| match e {
                Event::Token { kind, .. } => Some(crate::kind::is_trivia(*kind)),
                Event::Start(_) | Event::Finish | Event::Missing => None,
            })
            .unwrap_or(false)
    }

    /// Try each of `parsers` from the same savepoint `sp` (already
    /// captured by the caller so leading trivia/state is identical for
    /// every candidate); return the farthest-advancing success.
    /// First-registered wins on a tied end position. ORACLE-PORT
    /// `longestMatchFn`/`longestMatchStep` (Basic.lean): ties in real
    /// Lean collapse into a `choice` node; M3a's recorded,
    /// spec-documented divergence is first-wins instead (§risks,
    /// revisited in M3b).
    ///
    /// Restores to `sp` after every attempt (including the winner) —
    /// the caller splices the winning slice back in itself, since a
    /// trailing-loop caller additionally needs to insert a wrapping
    /// `Start` before doing so (the Pratt wrap), which a generic
    /// helper can't do on its own.
    fn longest_match(&mut self, sp: &Savepoint, parsers: &[Prim]) -> Option<MatchWinner> {
        let mut best: Option<MatchWinner> = None;
        for (i, p) in parsers.iter().enumerate() {
            self.restore(sp);
            if self.run(p).is_ok() {
                let better = match &best {
                    Some(w) => self.pos > w.end,
                    None => true,
                };
                if better {
                    best = Some(MatchWinner {
                        idx: i,
                        events: self.events[sp.events..].to_vec(),
                        errors: self.errors[sp.errors..].to_vec(),
                        end: self.pos,
                        lhs_prec: self.lhs_prec,
                    });
                }
            }
        }
        self.restore(sp);
        best
    }

    /// The Pratt driver: a category's leading parse (longest match over
    /// the dispatched leading candidates) followed by the trailing
    /// loop (repeated longest match over trailing candidates whose
    /// precedence gates admit the current `prec`/`lhs_prec`, each
    /// winner retroactively wrapping the already-parsed left-hand
    /// side). ORACLE-PORT `prattParser`/`leadingParser`/`trailingLoop`
    /// (Basic.lean).
    fn category(&mut self, name: &str, rbp: u32) -> PResult {
        let Some(cat) = self.snap_category(name) else {
            let at = self.pos;
            return Err(self.fail_expecting(&format!("<category {name}>"), at));
        };
        if self.cat_depth >= MAX_CATEGORY_DEPTH {
            // Untrusted-input totality: `Category` is the ONE place
            // input (nested parens, deeply chained trailing forms,
            // …) can drive recursion depth — see `MAX_CATEGORY_DEPTH`.
            let at = self.pos;
            return Err(self.fail_expecting("<max recursion depth exceeded>", at));
        }
        self.cat_depth += 1;
        let saved_prec = self.prec;
        self.prec = rbp;
        let r = (|| {
            // Captured BEFORE the lookahead `peek_significant` below —
            // Task 8 review fix: on TOTAL leading-dispatch failure (no
            // candidate matches at all — e.g. `cat("term", ..)` tried
            // as one `OrElse` alternative among several, with the next
            // token separated from the previous one by whitespace), the
            // category must look like a completely NON-consuming
            // failure to its caller, exactly like a plain `Prim::Ident`/
            // `expect_atom` mismatch already does (`peek_for_match`'s
            // own pre-peek savepoint). Without this, `peek_significant`
            // permanently emits the intervening whitespace as a trivia
            // event and advances `self.pos` as a side effect REGARDLESS
            // of whether dispatch then finds anything — so a failed
            // `category()` call used to leak that phantom "consumption"
            // to its caller, which made an enclosing `OrElse`/`many1`
            // wrongly treat a clean "nothing matched here" as a
            // consuming error instead of backtracking/stopping. Found
            // via `Term.fun`'s `many1(funBinder)`: the funBinder
            // fallback `cat("term", maxPrec)` tried (and failed) against
            // the `=>` token, permanently consuming the space before it
            // — `many1` then aborted with a hard error instead of
            // cleanly stopping after the one binder it already had.
            let entry_sp = self.save();
            // ---- leading: longest match over dispatched candidates --
            // `lhs_events` is captured AFTER `peek_significant` so any
            // leading trivia it scans (emitted directly into
            // `self.events`) sits BEFORE this index — consistent with
            // the no-wrap (bare) case, where that trivia is a sibling
            // of the leading node rather than swallowed into it. A
            // later trailing wrap retroactively opens `Event::Start` at
            // `lhs_events`; capturing it here keeps the leading trivia
            // OUTSIDE that wrap too, matching the bare case instead of
            // diverging from it (e.g. `( a + b)`'s leading space before
            // `a` must sit outside `add`, exactly as it sits outside
            // the bare atom in `( a )`).
            let (t, at) = self.peek_significant();
            let lhs_events = self.events.len();
            let text = &self.src[at..at + t.len as usize];
            let idxs = dispatch(cat, text, t.kind, true);
            let parsers: Vec<Prim> = idxs
                .iter()
                .map(|&i| cat.leading_parsers[i].clone())
                .collect();
            // ORACLE-PORT `runLongestMatchParser` (Basic.lean:1403):
            // "we initialize [lhsPrec] to maxPrec in the leading case"
            // — a leading candidate that is a real `leadingNode`
            // (`Prim::Node` with `Some(prec)`) overrides this on success
            // (`self.lhs_prec = prec.unwrap_or(0)`, the `Prim::Node` run
            // arm above); one that's a bare token/leaf parser
            // (`leading_raw`'s `Prim::Ident`/`NumLit`/etc — no `Node`
            // wrap at all) never touches `lhs_prec`, so without this
            // pre-seed it would leak whatever `lhs_prec` happened to
            // hold from unrelated earlier parsing. `Term.app`'s
            // trailing gate (`lhs_prec >= MAX_PREC`, Task 8) is the
            // first production that actually exercises this: a bare
            // ident head (`f` in `f a b c`) must count as "MAX_PREC
            // strength" for application to fire at all.
            let mut sp = self.save();
            sp.lhs_prec = crate::grammar::MAX_PREC;
            match self.longest_match(&sp, &parsers) {
                Some(w) => {
                    self.events.extend(w.events);
                    self.errors.extend(w.errors);
                    self.pos = w.end;
                    self.lhs_prec = w.lhs_prec;
                }
                None => {
                    let at = self.pos;
                    let f = self.fail_expecting(&format!("<{name}>"), at);
                    self.restore(&entry_sp);
                    return Err(f);
                }
            }

            // ---- trailing loop --------------------------------------
            loop {
                let (t, at) = self.peek_significant();
                if t.kind == TokenKind::Eof {
                    break;
                }
                let text = &self.src[at..at + t.len as usize];
                let idxs = dispatch(cat, text, t.kind, false);
                let qualifying: Vec<usize> = idxs
                    .into_iter()
                    .filter(|&idx| match &cat.trailing_parsers[idx] {
                        Prim::TrailingNode { prec, lhs_prec, .. } => {
                            *prec >= self.prec && self.lhs_prec >= *lhs_prec
                        }
                        _ => unreachable!("trailing entries are TrailingNode"),
                    })
                    .collect();
                if qualifying.is_empty() {
                    break;
                }
                let bodies: Vec<Prim> = qualifying
                    .iter()
                    .map(|&idx| match &cat.trailing_parsers[idx] {
                        Prim::TrailingNode { body, .. } => (**body).clone(),
                        _ => unreachable!(),
                    })
                    .collect();
                let sp = self.save();
                match self.longest_match(&sp, &bodies) {
                    // ORACLE-PORT `trailingLoop` (Basic.lean:1943-1946):
                    // "Discard non-consuming parse errors and break the
                    // trailing loop instead, restoring `left`. This is
                    // necessary for fallback parsers like `app` that
                    // pretend to be always applicable." A winning
                    // candidate that consumed no input (`w.end ==
                    // sp.pos`) must NOT wrap `left` — wrapping would
                    // requalify next iteration and loop forever (and
                    // grow the event stream unboundedly) whenever a
                    // trailing production's body can succeed
                    // zero-width. `self.longest_match` already restored
                    // to `sp` internally, so there is nothing of the
                    // winner's to undo here — just stop, leaving the
                    // existing lhs as the final result.
                    Some(w) if w.end == sp.pos => break,
                    Some(w) => {
                        let idx = qualifying[w.idx];
                        let Prim::TrailingNode { kind, prec, .. } = &cat.trailing_parsers[idx]
                        else {
                            unreachable!()
                        };
                        self.events.extend(w.events);
                        self.errors.extend(w.errors);
                        self.pos = w.end;
                        // The Pratt wrap: the lhs subtree (and every
                        // earlier wrap around it) already sits at
                        // `lhs_events`; retroactively opening a `Start`
                        // there makes the new node's first child be
                        // that ENTIRE existing subtree, with the just-
                        // parsed body's events (appended above) as the
                        // rest of its children.
                        self.events.insert(lhs_events, Event::Start(*kind));
                        self.events.push(Event::Finish);
                        self.lhs_prec = *prec;
                    }
                    None => break,
                }
            }
            Ok(())
        })();
        self.prec = saved_prec;
        self.cat_depth -= 1;
        r
    }

    // ---- output -------------------------------------------------------
    /// Fold the event stream into a lossless tree, using the
    /// snapshot's own `Arc<KindInterner>` (cloned once at `Ps::new`).
    pub(crate) fn finish_into_tree(self) -> (SyntaxTree, Vec<ParseError>) {
        let tree = build_tree(self.src, &self.events, self.kinds.clone());
        (tree, self.errors)
    }
}

/// Collect the `leading`/`trailing` candidate indices (registration
/// order) whose `FirstTok` matches the upcoming token — `FirstTok::Any`
/// entries are unindexed and always tried, alongside whichever
/// specific-token entries matched (ORACLE-PORT `PrattParsingTables`:
/// the indexed table lookup plus the always-tried `leadingParsers`/
/// `trailingParsers` list, collapsed here into one paired vector — see
/// `Category`'s doc comment).
fn dispatch(cat: &Category, text: &str, kind: TokenKind, leading: bool) -> Vec<usize> {
    let table = if leading { &cat.leading } else { &cat.trailing };
    table
        .iter()
        .filter_map(|(f, idx)| {
            let matches = match f {
                FirstTok::Any => true,
                // A token-table symbol lexes as `Atom` (even when
                // ident-shaped, e.g. `do`/`then` — ORACLE-PORT
                // `next_token`'s munch-competition rule in lex.rs), so
                // the `Atom` arm covers every real `Prim::Symbol`. The
                // `Ident`-with-matching-text arm is what makes
                // `Prim::NonReservedSymbol` (`level`'s `max`/`imax`)
                // dispatchable at all: ORACLE-PORT `nonReservedSymbolInfo`
                // (Basic.lean) — `nonReservedSymbol sym (includeIdent :=
                // true)` sets `firstTokens := .tokens [sym, "ident"]`,
                // a DUAL registration, precisely because `sym`'s text is
                // deliberately never harvested into the token table
                // (grammar.rs's `walk_symbols` doc comment) and so can
                // only ever lex as a plain `Ident`, never an `Atom`. A
                // real `Symbol`'s text, by contrast, always lexes as
                // `Atom` once harvested (never `Ident`), so this second
                // arm is a dead branch for it — extending the match
                // costs real `Symbol` dispatch nothing and is exactly
                // what makes a `NonReservedSymbol`-led production
                // reachable at all. `first_tok` maps both `Symbol` and
                // `NonReservedSymbol` to the same `FirstTok::Sym`
                // (grammar.rs), so this one arm covers both.
                FirstTok::Sym(s) => {
                    (kind == TokenKind::Atom && s == text)
                        || (kind == TokenKind::Ident && s == text)
                }
                FirstTok::Ident => kind == TokenKind::Ident,
                FirstTok::Num => kind == TokenKind::Num,
                FirstTok::Scientific => kind == TokenKind::Scientific,
                FirstTok::Str => kind == TokenKind::Str,
                FirstTok::Char => kind == TokenKind::Char,
                FirstTok::NameLit => kind == TokenKind::NameLit,
            };
            matches.then_some(*idx)
        })
        .collect()
}

#[cfg_attr(not(test), allow(dead_code))]
fn trivia_kind(k: TokenKind) -> SyntaxKind {
    match k {
        TokenKind::Whitespace => crate::kind::KIND_WHITESPACE,
        TokenKind::LineComment => crate::kind::KIND_LINE_COMMENT,
        TokenKind::BlockComment => crate::kind::KIND_BLOCK_COMMENT,
        _ => unreachable!("trivia_kind on non-trivia"),
    }
}

#[cfg(test)]
impl<'a> Ps<'a> {
    /// Test-only constructor: pre-interns the literal-leaf kind names
    /// `lit`/`field_idx` look up by name, wraps `table`/`kinds` (as
    /// they stand at this call) into a category-less `GrammarSnapshot`
    /// (leaked for the `'a` borrow `Ps` needs — fine, this only runs in
    /// tests), matching what real code gets for free from
    /// `SnapshotBuilder`.
    pub(crate) fn new_for_test(src: &'a str, table: TokenTable, kinds: &mut KindInterner) -> Self {
        for name in ["num", "scientific", "str", "char", "name", "fieldIdx"] {
            kinds.intern(name);
        }
        let snap = crate::grammar::GrammarSnapshot::for_test(table, kinds.clone());
        let snap: &'a crate::grammar::GrammarSnapshot = Box::leak(Box::new(snap));
        Ps::new(src, snap)
    }

    pub(crate) fn finish_into_tree_for_test(self) -> (SyntaxTree, Vec<ParseError>) {
        self.finish_into_tree()
    }

    pub(crate) fn furthest_for_test(&self) -> (usize, Vec<String>) {
        (self.furthest_pos, self.furthest_expected.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grammar::*;
    use crate::kind::KindInterner;
    use crate::lex::TokenTable;
    use std::sync::Arc;

    /// Run `p` against `src` with tokens from `toks`; return
    /// (canon-ish sexpr of the tree, errors) for terse assertions. A
    /// failed top-level `run` is recorded as exactly one E0301 (mirrors
    /// what the real `recover_command` (Task 7/11) does at command
    /// granularity) so tests can assert on error *counts* meaningfully;
    /// a failure some inner `OrElse`/`Atomic` backtracked past does NOT
    /// get one, since `run` only returns `Err` when nothing recovered.
    fn run_toy(src: &str, toks: &[&str], p: &Prim, kinds: &mut KindInterner) -> (String, usize) {
        let mut table = TokenTable::default();
        for t in toks {
            table.insert(t);
        }
        let root = kinds.intern("root");
        let mut ps = Ps::new_for_test(src, table, kinds);
        ps.start(root);
        if ps.run(p).is_err() {
            ps.push_furthest_error();
        }
        ps.finish();
        let (tree, errors) = ps.finish_into_tree_for_test();
        (sexpr(&tree), errors.len())
    }

    /// Hoisted so Task 6's `parse_cat` can sexpr a single sub-node
    /// (the `Category` call's result) rather than the whole tree.
    fn sexpr_node(n: &crate::tree::SyntaxNode, k: &KindInterner, out: &mut String) {
        out.push('(');
        out.push_str(k.name(n.kind()));
        for el in n.children_with_tokens() {
            match el {
                rowan::NodeOrToken::Node(c) => {
                    out.push(' ');
                    sexpr_node(&c, k, out);
                }
                rowan::NodeOrToken::Token(t) => {
                    use crate::kind::*;
                    if is_trivia(t.kind()) {
                        continue;
                    }
                    out.push(' ');
                    if t.kind() == KIND_IDENT {
                        out.push_str(t.text());
                    } else {
                        out.push('\'');
                        out.push_str(t.text());
                        out.push('\'');
                    }
                }
            }
        }
        out.push(')');
    }

    fn sexpr(tree: &crate::tree::SyntaxTree) -> String {
        let mut out = String::new();
        sexpr_node(&tree.root(), &tree.kinds, &mut out);
        out
    }

    /// Task 6: parse `src` by running `Prim::Category { rbp: 0 }` for
    /// the snapshot's (single, in these tests) category, wrapped in a
    /// scaffold `null` root so `build_tree`'s single-root contract
    /// holds; sexpr just the category's own resulting node.
    fn parse_cat(snap: &GrammarSnapshot, src: &str) -> String {
        let name = snap
            .categories
            .keys()
            .next()
            .expect("test snapshot registers exactly one category")
            .clone();
        let mut ps = Ps::new(src, snap);
        ps.start(KIND_NULL);
        if ps.run(&Prim::Category { name, rbp: 0 }).is_err() {
            ps.push_furthest_error();
        }
        ps.finish();
        let (tree, _errors) = ps.finish_into_tree();
        let root = tree.root();
        let child = root
            .first_child()
            .expect("category call produced exactly one child node");
        let mut out = String::new();
        sexpr_node(&child, &tree.kinds, &mut out);
        out
    }

    /// Trivia-VISIBLE variant of `sexpr_node`/`parse_cat` — Finding 2's
    /// regression test needs to see exactly where whitespace events
    /// land (inside vs. outside a trailing wrap), which the trivia-
    /// stripping `sexpr_node` above can't distinguish. Every trivia
    /// token (kind-agnostic — whitespace/line/block comment all render
    /// the same) prints as the literal marker `<ws>` in tree position.
    fn sexpr_node_with_trivia(n: &crate::tree::SyntaxNode, k: &KindInterner, out: &mut String) {
        out.push('(');
        out.push_str(k.name(n.kind()));
        for el in n.children_with_tokens() {
            match el {
                rowan::NodeOrToken::Node(c) => {
                    out.push(' ');
                    sexpr_node_with_trivia(&c, k, out);
                }
                rowan::NodeOrToken::Token(t) => {
                    use crate::kind::*;
                    out.push(' ');
                    if is_trivia(t.kind()) {
                        out.push_str("<ws>");
                    } else if t.kind() == KIND_IDENT {
                        out.push_str(t.text());
                    } else {
                        out.push('\'');
                        out.push_str(t.text());
                        out.push('\'');
                    }
                }
            }
        }
        out.push(')');
    }

    fn parse_cat_with_trivia(snap: &GrammarSnapshot, src: &str) -> String {
        let name = snap
            .categories
            .keys()
            .next()
            .expect("test snapshot registers exactly one category")
            .clone();
        let mut ps = Ps::new(src, snap);
        ps.start(KIND_NULL);
        if ps.run(&Prim::Category { name, rbp: 0 }).is_err() {
            ps.push_furthest_error();
        }
        ps.finish();
        let (tree, _errors) = ps.finish_into_tree();
        let root = tree.root();
        let child = root
            .first_child()
            .expect("category call produced exactly one child node");
        let mut out = String::new();
        sexpr_node_with_trivia(&child, &tree.kinds, &mut out);
        out
    }

    #[test]
    fn seq_and_symbols() {
        let mut k = KindInterner::new();
        let decl = k.intern("decl");
        let p = Prim::Node {
            kind: decl,
            prec: None,
            body: Arc::new(seq([sym("def"), Prim::Ident, sym(":="), Prim::NumLit])),
        };
        let (s, errs) = run_toy("def x := 42", &["def", ":="], &p, &mut k);
        assert_eq!(s, "(root (decl 'def' x ':=' (num '42')))");
        assert_eq!(errs, 0);
    }

    #[test]
    fn optional_and_many_wrap_in_null_nodes() {
        let mut k = KindInterner::new();
        let p = seq([opt(sym("@")), many(Prim::Ident)]);
        let (s, _) = run_toy("a b c", &["@"], &wrap_root(&mut k, p), &mut k);
        assert_eq!(s, "(root (r (null) (null a b c)))");
    }

    #[test]
    fn orelse_backtracks_only_without_consumption() {
        let mut k = KindInterner::new();
        // alt1 consumes "def" then fails on missing ":=" → consuming
        // failure → alt2 must NOT be tried.
        let p = or_else([seq([sym("def"), sym(":=")]), sym("def")]);
        let (_, errs) = run_toy("def x", &["def", ":="], &wrap_root(&mut k, p), &mut k);
        assert_eq!(errs, 1);
        // With atomic(alt1) the same input succeeds via alt2.
        let p = or_else([atomic(seq([sym("def"), sym(":=")])), sym("def")]);
        let (_, errs) = run_toy("def x", &["def", ":="], &wrap_root(&mut k, p), &mut k);
        assert_eq!(errs, 0);
    }

    #[test]
    fn sepby1_interleaves_flat() {
        let mut k = KindInterner::new();
        let p = sep_by1(Prim::Ident, ",");
        let (s, _) = run_toy("a, b, c", &[","], &wrap_root(&mut k, p), &mut k);
        assert_eq!(s, "(root (r (null a ',' b ',' c)))");
    }

    #[test]
    fn failure_reports_furthest_position_with_expected_set() {
        let mut k = KindInterner::new();
        // Interned before `Ps` borrows `k` (borrow-order fix over the
        // plan's inline sketch, which interned `root` after the `Ps`
        // borrow started — doesn't compile as literally written there).
        let root = k.intern("root");
        let p = seq([sym("def"), Prim::Ident, sym(":=")]);
        let mut table = TokenTable::default();
        table.insert("def");
        table.insert(":=");
        let mut ps = Ps::new_for_test("def x +", table, &mut k);
        ps.start(root);
        let r = ps.run(&p);
        assert!(r.is_err());
        let (pos, expected) = ps.furthest_for_test();
        assert_eq!(pos, 6); // at the '+'
        assert!(expected.iter().any(|e| e == "':='"));
    }

    #[test]
    fn many_propagates_a_consuming_inner_failure_and_stays_balanced() {
        // ORACLE-PORT `manyFn`: `s.mkNode nullKind iniSz` wraps the
        // loop's result UNCONDITIONALLY, error or not — a consuming
        // failure inside an item must still close the `null` node.
        // (This is the regression case for a real bug found while
        // porting the plan's inline `many_impl`: an early `return
        // Err(f)` inside the loop skipped the closing `self.finish()`,
        // leaving a dangling `Start` event that `build_tree`'s balance
        // `debug_assert` would catch — i.e. this test panics without
        // the fix.)
        let mut k = KindInterner::new();
        let p = many(seq([sym("("), sym(")")]));
        let (s, errs) = run_toy("() () (x", &["(", ")"], &wrap_root(&mut k, p), &mut k);
        assert_eq!(s, "(root (r (null '(' ')' '(' ')' '(')))");
        assert_eq!(errs, 1);
    }

    #[test]
    fn orelse_tries_the_next_alternative_past_leading_trivia() {
        // A leaf mismatch must not count leading trivia it had to scan
        // through as "consumption" (ORACLE-PORT `Parser/Types.lean`
        // `mkUnexpectedTokenErrors`: resets `s.pos` to the PRE-token
        // position on a mismatch) — otherwise `OrElse` refuses to try
        // the next alternative whenever the failing one was preceded by
        // whitespace, which is nearly every alternative in real source.
        let mut k = KindInterner::new();
        let p = or_else([sym("foo"), sym("bar")]);
        let (s, errs) = run_toy(" bar", &["foo", "bar"], &wrap_root(&mut k, p), &mut k);
        assert_eq!(s, "(root (r 'bar'))");
        assert_eq!(errs, 0);
    }

    #[test]
    fn many1_tolerates_one_zero_width_item_but_rejects_a_second() {
        // ORACLE-PORT `manyAux`: a zero-width successful item, repeated,
        // is flagged ("invalid 'many' parser combinator application,
        // parser did not consume anything") rather than looped forever;
        // `many1`'s mandatory FIRST item is exempt (that exemption is
        // what lets `many1(optional(...))` express "at least one,
        // possibly empty").
        let mut k = KindInterner::new();
        let p = many1(opt(sym("@")));
        let (_, errs) = run_toy("x", &["@"], &wrap_root(&mut k, p), &mut k);
        assert_eq!(errs, 1);
    }

    #[test]
    fn sep_by_rejects_a_trailing_separator_when_not_allowed() {
        let mut k = KindInterner::new();
        let p = sep_by1(Prim::Ident, ",");
        let (_, errs) = run_toy("a, b,", &[","], &wrap_root(&mut k, p), &mut k);
        assert_eq!(errs, 1);
    }

    fn wrap_root(k: &mut KindInterner, body: Prim) -> Prim {
        let r = k.intern("r");
        Prim::Node {
            kind: r,
            prec: None,
            body: Arc::new(body),
        }
    }

    // ---- Task 6: categories, Pratt precedence, position/prec, ---------
    // ---- GrammarSnapshot fingerprint. ----------------------------------

    /// A miniature Pratt category: atoms `a`; prefix `- e` (prec 75);
    /// left-assoc `e + e` (prec 65); right-assoc `e ^ e` (prec 75).
    fn arith_snapshot() -> crate::grammar::GrammarSnapshot {
        let mut b = SnapshotBuilder::new();
        b.category("term");
        b.leading2("term", "lit", MAX_PREC, Prim::Ident);
        b.leading2("term", "neg", 75, seq([sym("-"), cat("term", 75)]));
        b.trailing2("term", "add", 65, 65, seq([sym("+"), cat("term", 66)]));
        b.trailing2("term", "pow", 75, 76, seq([sym("^"), cat("term", 75)]));
        b.finish()
    }

    #[test]
    fn pratt_precedence_and_associativity() {
        let snap = arith_snapshot();
        // Idents parse via the "lit" leading node, so leaves print as
        // (lit x). a + b + c → left assoc (rhs at 66):
        assert_eq!(
            parse_cat(&snap, "a + b + c"),
            "(add (add (lit a) '+' (lit b)) '+' (lit c))"
        );
        // a ^ b ^ c → right assoc (rhs at 75):
        assert_eq!(
            parse_cat(&snap, "a ^ b ^ c"),
            "(pow (lit a) '^' (pow (lit b) '^' (lit c)))"
        );
        // - a + b → prefix binds tighter:
        assert_eq!(
            parse_cat(&snap, "- a + b"),
            "(add (neg '-' (lit a)) '+' (lit b))"
        );
        // a + - b → the rhs of + parses the prefix:
        assert_eq!(
            parse_cat(&snap, "a + - b"),
            "(add (lit a) '+' (neg '-' (lit b)))"
        );
    }

    #[test]
    fn longest_match_picks_the_farthest_leading_parse() {
        let mut b = SnapshotBuilder::new();
        b.category("c");
        b.leading2("c", "short", MAX_PREC, sym("x"));
        b.leading2("c", "long", MAX_PREC, seq([sym("x"), sym("!")]));
        let snap = b.finish();
        assert_eq!(parse_cat(&snap, "x !"), "(long 'x' '!')");
        assert_eq!(parse_cat(&snap, "x"), "(short 'x')");
    }

    #[test]
    fn with_position_col_gt() {
        let mut b = SnapshotBuilder::new();
        b.category("c");
        // "block" = 'do' then many1 idents, each on a column > do's.
        b.leading2(
            "c",
            "block",
            MAX_PREC,
            Prim::WithPosition(Arc::new(seq([
                sym("do"),
                many1(seq([Prim::CheckColGt, Prim::Ident])),
            ]))),
        );
        let snap = b.finish();
        assert_eq!(parse_cat(&snap, "do a\n   b"), "(block 'do' (null a b))");
        // `b` at column 0 is OUTSIDE the block: many1 stops after `a`.
        assert_eq!(parse_cat(&snap, "do a\nb"), "(block 'do' (null a))");
    }

    #[test]
    fn snapshot_fingerprint_is_stable_and_grammar_sensitive() {
        let s1 = arith_snapshot();
        let s2 = arith_snapshot();
        assert_eq!(s1.fingerprint(), s2.fingerprint());
        let mut b = SnapshotBuilder::new();
        b.category("term");
        b.leading2("term", "lit", MAX_PREC, Prim::Ident);
        let s3 = b.finish();
        assert_ne!(s1.fingerprint(), s3.fingerprint());
    }

    #[test]
    fn category_leading_match_preserves_errors_from_the_winning_candidate() {
        // Regression test for a real bug found while implementing this
        // task: `longest_match`'s per-candidate savepoint restore
        // truncates `self.errors` before EVERY attempt (needed so a
        // losing candidate's diagnostics don't leak) — but the WINNING
        // candidate can itself have pushed legitimate errors (e.g. an
        // embedded lexer error) that must survive that final restore.
        // An unterminated raw string still lexes to a `Str` token (with
        // an attached `LexError`) and successfully completes the
        // `StrLit` leaf parse, so this exercises exactly that path.
        let mut b = SnapshotBuilder::new();
        b.category("c");
        b.leading2("c", "s", MAX_PREC, Prim::StrLit);
        let snap = b.finish();
        let src = "r\"unterminated";
        let mut ps = Ps::new(src, &snap);
        ps.start(KIND_NULL);
        let r = ps.run(&Prim::Category {
            name: "c".to_string(),
            rbp: 0,
        });
        assert!(r.is_ok(), "the leaf parse itself should succeed: {r:?}");
        assert_eq!(
            ps.errors.len(),
            1,
            "the embedded unterminated-raw-string lex error must survive \
             the leading longest-match splice, not be discarded"
        );
        assert_eq!(ps.errors[0].code, "E0302");
    }

    #[test]
    fn sep_by_indent_semicolon_same_column_no_semicolon_needed() {
        // ORACLE-PORT `Term/Basic.lean` `sepByIndentSemicolon`: items on
        // their own line at the marker's column don't need `;`;
        // two on the SAME line do.
        let mut b = SnapshotBuilder::new();
        b.category("c");
        b.leading2(
            "c",
            "seq",
            MAX_PREC,
            Prim::WithPosition(Arc::new(Prim::SepByIndentSemicolon(Arc::new(Prim::Ident)))),
        );
        let snap = b.finish();
        assert_eq!(parse_cat(&snap, "a\nb\nc"), "(seq (null a b c))");
        assert_eq!(parse_cat(&snap, "a; b; c"), "(seq (null a ';' b ';' c))");
        assert_eq!(parse_cat(&snap, "a; b;"), "(seq (null a ';' b ';'))");
    }

    #[test]
    fn adversarial_nesting_terminates_without_overflow() {
        // Untrusted-input totality: `Category` recursion is the ONE
        // place input can drive parser recursion depth (nested parens
        // here). Well past `MAX_CATEGORY_DEPTH`, this must return an
        // error — gracefully, never panicking or overflowing the
        // stack (if it does, this test crashes the process rather
        // than failing an assert, which is exactly the property being
        // checked).
        let mut b = SnapshotBuilder::new();
        b.category("e");
        b.leading2("e", "atom", MAX_PREC, Prim::Ident);
        b.leading2(
            "e",
            "paren",
            MAX_PREC,
            seq([sym("("), cat("e", 0), sym(")")]),
        );
        let snap = b.finish();
        let name = snap.categories.keys().next().unwrap().clone();

        let deep = "(".repeat(10_000) + "x" + &")".repeat(10_000);
        let mut ps = Ps::new(&deep, &snap);
        let r = ps.run(&Prim::Category {
            name: name.clone(),
            rbp: 0,
        });
        assert!(r.is_err(), "adversarial depth must fail, not hang/crash");

        // A depth well within the cap still parses correctly, with the
        // expected nesting.
        let depth = 10usize;
        let shallow = "(".repeat(depth) + "x" + &")".repeat(depth);
        let mut expected = "(atom x)".to_string();
        for _ in 0..depth {
            expected = format!("(paren '(' {expected} ')')");
        }
        assert_eq!(parse_cat(&snap, &shallow), expected);
    }

    // ---- Task 6 review fixes ------------------------------------------

    #[test]
    fn trailing_loop_breaks_on_zero_progress_instead_of_looping_forever() {
        // ORACLE-PORT `trailingLoop` (Basic.lean:1943-1946): "Discard
        // non-consuming parse errors and break the trailing loop
        // instead, restoring `left`. This is necessary for fallback
        // parsers like `app` that pretend to be always applicable."
        // A toy trailing production whose body is `opt(sym("!"))` can
        // WIN the trailing longest-match with zero tokens consumed
        // (the `!` just isn't there — `Optional` always succeeds).
        // Without the zero-progress guard this wraps `left`, loops
        // back to the top of the trailing loop, qualifies again
        // (nothing changed), and wraps forever — infinite loop, plus
        // unbounded event-stream growth. This test would hang forever
        // pre-fix; post-fix it terminates and leaves the zero-width
        // candidate unapplied, with `y` unconsumed.
        let mut b = SnapshotBuilder::new();
        b.category("c");
        b.leading2("c", "lit", MAX_PREC, Prim::Ident);
        b.trailing2("c", "wrap", 0, 0, opt(sym("!")));
        let snap = b.finish();

        // Zero-progress winner: discarded, `x` stands as-is.
        assert_eq!(parse_cat(&snap, "x y"), "(lit x)");
        // Genuine progress: the same production DOES wrap when its
        // body actually consumes something.
        assert_eq!(parse_cat(&snap, "x !"), "(wrap (lit x) (null '!'))");
    }

    #[test]
    fn leading_trivia_stays_outside_a_trailing_wrap_like_it_does_in_the_bare_case() {
        // Review finding 2: `lhs_events` (the retroactive `Start`
        // insertion point for a Pratt trailing wrap) used to be
        // captured BEFORE the leading `peek_significant()`, so the
        // first token's leading trivia (emitted BY that peek) landed
        // after the capture point — a later trailing wrap's `Start`
        // insert at `lhs_events` would then pull that trivia INSIDE
        // the wrap, even though the bare (no-wrap) case leaves the
        // very same trivia OUTSIDE the leading node as a sibling.
        // Fixed by capturing `lhs_events` AFTER the leading peek, so
        // leading trivia always sits outside any later wrap — same as
        // the bare case.
        let mut b = SnapshotBuilder::new();
        b.category("c");
        b.leading2(
            "c",
            "paren",
            MAX_PREC,
            seq([sym("("), cat("c", 0), sym(")")]),
        );
        b.leading2("c", "lit", MAX_PREC, Prim::Ident);
        b.trailing2("c", "add", 65, 65, seq([sym("+"), cat("c", 66)]));
        let snap = b.finish();

        // Bare case (no trailing wrap): the space after '(' sits
        // outside `(lit a)`, as a sibling.
        assert_eq!(
            parse_cat_with_trivia(&snap, "( a )"),
            "(paren '(' <ws> (lit a) <ws> ')')"
        );
        // Trailing-wrap case: the SAME leading space must land in the
        // SAME place — outside `(add ...)`, not swallowed as its
        // first (misattributed) child.
        assert_eq!(
            parse_cat_with_trivia(&snap, "( a + b)"),
            "(paren '(' <ws> (add (lit a) <ws> '+' <ws> (lit b)) ')')"
        );
    }

    #[test]
    fn non_reserved_symbol_does_not_reserve_its_token_snapshot_wide() {
        // Review finding 3: `nonReservedSymbolInfo` (Basic.lean:
        // 1143-1149) leaves `collectTokens` at `ParserInfo`'s default
        // no-op (Types.lean:499-500) — unlike `symbolInfo`
        // (Basic.lean:1105-1108), which explicitly registers its
        // token. So a `NonReservedSymbol`'s text must keep lexing as
        // plain `Ident` everywhere EXCEPT where the combinator itself
        // is positioned to match it contextually (mirrors real Lean
        // patterns like `atomic ("(" >> nonReservedSymbol "priority")
        // >> ...>`, Command.lean:65, where the enclosing symbol
        // anchors dispatch and the contextual keyword never touches
        // the token table).
        let mut b = SnapshotBuilder::new();
        b.category("c");
        b.leading2(
            "c",
            "kw",
            MAX_PREC,
            seq([
                sym("("),
                Prim::NonReservedSymbol("dependent".to_string()),
                sym(")"),
            ]),
        );
        b.leading2("c", "lit", MAX_PREC, Prim::Ident);
        let snap = b.finish();

        // Contextually, inside the parens, "dependent" matches the
        // `NonReservedSymbol` combinator.
        assert_eq!(
            parse_cat(&snap, "( dependent )"),
            "(kw '(' 'dependent' ')')"
        );
        // In an unrelated position (bare, no parens), the very same
        // text still lexes and parses as a plain identifier — proving
        // it was never reserved snapshot-wide.
        assert_eq!(parse_cat(&snap, "dependent"), "(lit dependent)");
    }
}
