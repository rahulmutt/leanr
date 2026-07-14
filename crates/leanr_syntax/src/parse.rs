//! The Prim interpreter (spec §Architecture / parse). One mutable state
//! (`Ps`) over the event list; speculation = truncate-to-savepoint;
//! Pratt trailing wrap = insert Start at the lhs event index (Task 6).
//! Failure carries no data — the state records the furthest failure
//! position + expected set for diagnostics (Lean errorMsg merging).
//!
//! `Ps` borrows only a `TokenTable` + `KindInterner` here, NOT a
//! `GrammarSnapshot` (that type is Task 6's — it doesn't exist yet).
//! `Category`/`TrailingNode` and the position/precedence checks below
//! are `unimplemented!` until Task 6 lands and rewires this state to
//! hold `&GrammarSnapshot` in place of the bare table + interner.

use std::sync::Arc;

use crate::grammar::Prim;
use crate::kind::{KindInterner, SyntaxKind, KIND_ATOM, KIND_GROUP, KIND_IDENT, KIND_NULL};
use crate::lex::{next_token, Token, TokenKind, TokenTable};
use crate::tree::{build_tree, Event, SyntaxTree};

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
    table: &'a TokenTable,
    kinds: &'a KindInterner,
    events: Vec<Event>,
    pub(crate) errors: Vec<ParseError>,
    furthest_pos: usize,
    furthest_expected: Vec<String>,
    /// Current right-binding power: `Category` sets it on recursion,
    /// `Node`'s `prec` gate reads it. `Category` is Task 6's; until
    /// then this stays 0 and the gate below is a no-op (`np < 0` never
    /// holds for a `u32`).
    prec: u32,
    /// Precedence of the last completed leading/trailing node.
    lhs_prec: u32,
    /// `withPosition` stack: saved (line, col) of a position marker.
    /// Populated/read starting Task 6's `WithPosition`/`CheckColGt`.
    #[allow(dead_code)]
    pos_stack: Vec<(u32, u32)>,
    /// Byte offset of each line start (for column computation). Read
    /// starting Task 6's column/line position checks.
    #[allow(dead_code)]
    line_starts: Vec<usize>,
}

#[cfg_attr(not(test), allow(dead_code))]
pub(crate) struct Savepoint {
    pos: usize,
    events: usize,
    errors: usize,
    lhs_prec: u32,
}

#[cfg_attr(not(test), allow(dead_code))]
impl<'a> Ps<'a> {
    pub(crate) fn new(src: &'a str, table: &'a TokenTable, kinds: &'a KindInterner) -> Self {
        let mut line_starts = vec![0];
        for (i, b) in src.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(i + 1);
            }
        }
        Ps {
            src,
            pos: 0,
            table,
            kinds,
            events: Vec::new(),
            errors: Vec::new(),
            furthest_pos: 0,
            furthest_expected: Vec::new(),
            prec: 0,
            lhs_prec: 0,
            pos_stack: Vec::new(),
            line_starts,
        }
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
            let (t, err) = next_token(self.src, self.pos, self.table);
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
        if let (_, Some(e)) = next_token(self.src, self.pos, self.table) {
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
            // Task 6 fills these:
            Prim::Category { .. }
            | Prim::WithPosition(_)
            | Prim::CheckColGt
            | Prim::CheckColGe
            | Prim::CheckColEq
            | Prim::CheckLineEq
            | Prim::CheckPrec(_)
            | Prim::CheckLhsPrec(_)
            | Prim::CheckWsBefore
            | Prim::CheckNoWsBefore
            | Prim::Many1Indent(_)
            | Prim::SepByIndentSemicolon(_)
            | Prim::TrailingNode { .. } => {
                unimplemented!("Task 6: {:?}", std::mem::discriminant(p))
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

    // ---- output -------------------------------------------------------
    /// Fold the event stream into a lossless tree. `kinds` is normally
    /// the snapshot's own `Arc<KindInterner>` (Task 6) — the caller
    /// supplies it so `Ps` itself never needs to own one.
    pub(crate) fn finish_into_tree(
        self,
        kinds: Arc<KindInterner>,
    ) -> (SyntaxTree, Vec<ParseError>) {
        let tree = build_tree(self.src, &self.events, kinds);
        (tree, self.errors)
    }
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
    /// Test-only constructor: takes ownership of the token table
    /// (leaked for the `'a` borrow `Ps` needs — fine, this only runs in
    /// tests) and pre-interns the literal-leaf kind names `lit`/
    /// `field_idx` look up by name, which real code will get for free
    /// from Task 6's `SnapshotBuilder` (not built yet).
    pub(crate) fn new_for_test(
        src: &'a str,
        table: TokenTable,
        kinds: &'a mut KindInterner,
    ) -> Self {
        for name in ["num", "scientific", "str", "char", "name", "fieldIdx"] {
            kinds.intern(name);
        }
        let table: &'a TokenTable = Box::leak(Box::new(table));
        Ps::new(src, table, kinds)
    }

    pub(crate) fn finish_into_tree_for_test(self) -> (SyntaxTree, Vec<ParseError>) {
        let kinds = Arc::new(self.kinds.clone());
        self.finish_into_tree(kinds)
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

    fn sexpr(tree: &crate::tree::SyntaxTree) -> String {
        fn go(n: &crate::tree::SyntaxNode, k: &KindInterner, out: &mut String) {
            out.push('(');
            out.push_str(k.name(n.kind()));
            for el in n.children_with_tokens() {
                match el {
                    rowan::NodeOrToken::Node(c) => {
                        out.push(' ');
                        go(&c, k, out);
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
        let mut out = String::new();
        go(&tree.root(), &tree.kinds, &mut out);
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
}
