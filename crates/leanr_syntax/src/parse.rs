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

use std::collections::HashMap;
use std::sync::Arc;

use crate::grammar::{
    Category, CategoryDelta, FirstTok, GrammarSnapshot, LeadingIdentBehavior, Overlay, Prim,
};
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
///
/// **Runs the parse on its own, correctly sized worker thread.** The
/// parser recurses natively through nested input, so "never panic on
/// untrusted input" needs a known amount of native stack —
/// `MIN_STACK_BYTES`, against which `MAX_CATEGORY_DEPTH` is calibrated
/// (see both constants). That used to be an unchecked *precondition* on
/// this function's caller, which is the worst possible shape for a safety
/// contract: nothing verified it, the default environment violates it
/// (main thread 8 MiB, a `tokio` worker or a `libtest` thread 2 MiB), and
/// the failure mode is a SIGSEGV — strictly worse than the panic the
/// untrusted-input rule forbids (Task 11b review wave 2, Critical 2). So
/// the contract is now internal and unconditional: `parse_module` spawns a
/// `std::thread::Builder::new().stack_size(MIN_STACK_BYTES)` scoped worker
/// (`spawn_scoped`, std-only, stable since 1.63 — it borrows `src`/`snap`
/// without a `'static` bound, so this signature is unchanged) and joins
/// it. Callers need no stack discipline of their own. This is also, in
/// miniature, what real Lean does: it sizes its parser threads explicitly
/// (`lean -s/--tstack=<KB>`).
///
/// Cost: one thread spawn+join per module parse, measured at ~30-60 µs —
/// three orders of magnitude under a real module parse (the smallest
/// oracle fixture is ~0.5 ms; `Micro.lean` ~1 ms), so it is not a
/// meaningful tax on the only granularity this API offers.
///
/// A panic inside the worker is re-raised on the caller's thread
/// (`resume_unwind`) rather than swallowed: the never-panic property is
/// about *input*, not about masking genuine bugs.
pub fn parse_module(src: &str, snap: &GrammarSnapshot) -> ParseResult {
    std::thread::scope(|scope| {
        let worker = std::thread::Builder::new()
            .stack_size(MIN_STACK_BYTES)
            .spawn_scoped(scope, || parse_module_here(src, snap))
            // Not an untrusted-input failure path: the OS refusing a
            // thread is a resource condition, unrelated to the bytes being
            // parsed. A clean panic here is the right (and only honest)
            // outcome — the alternative, parsing inline on a stack of
            // unknown size, is the segfault this whole change removes.
            .expect("spawn the parse worker thread");
        match worker.join() {
            Ok(r) => r,
            Err(panic) => std::panic::resume_unwind(panic),
        }
    })
}

/// `parse_module`'s body, on whatever stack the caller is standing on.
/// Private on purpose: the public entry point is `parse_module`, which
/// guarantees that stack is `MIN_STACK_BYTES` (see there).
fn parse_module_here(src: &str, snap: &GrammarSnapshot) -> ParseResult {
    run_module(Ps::new(src, snap), snap)
}

/// Test-only entry point (M3b1 Task 6 brief interfaces: "a `pub(crate)`
/// variant of `parse_module` that accepts a pre-seeded overlay"):
/// installs `ov` on a fresh `Ps` before running the header + command
/// loop, so a test can exercise "a manually-installed overlay actually
/// changes parsing" directly — without Task 7's per-command growth loop
/// (parsing a `notation` command and folding its `NotationSpec` into the
/// overlay automatically), which is out of scope for this task.
///
/// Runs on the CALLER's stack, unlike `parse_module` (no
/// `MIN_STACK_BYTES` worker) — fine for the small fixtures this is used
/// with; every production parse still goes through `parse_module`.
#[cfg(test)]
pub(crate) fn parse_module_with_overlay(
    src: &str,
    snap: &GrammarSnapshot,
    ov: Overlay,
) -> ParseResult {
    let mut ps = Ps::new(src, snap);
    ps.install_overlay(ov);
    run_module(ps, snap)
}

/// Shared by `parse_module_here` and (test-only)
/// `parse_module_with_overlay`: header, then commands to EOF, then the
/// trailing `eoi` node — see `parse_module`'s own doc comment for the
/// full citation of what this reproduces. Takes an already-constructed
/// `Ps` so the only difference between the two callers is whether
/// `install_overlay` ran first.
fn run_module(mut ps: Ps<'_>, snap: &GrammarSnapshot) -> ParseResult {
    let kinds = snap.kinds();
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
            // Belt-and-suspenders zero-progress guard (M3a final-review
            // Minor finding (e)). This loop's termination currently
            // relies on a GRAMMAR property — every `command` leading
            // production starts with a mandatory keyword / `@[` / `/--`
            // / modifier, so a *successful* `command` parse can never
            // be zero-width today — rather than a LOCAL one enforced by
            // the loop itself. That's unlike every other repeating
            // combinator in this file (`many`/`many1`/`sep_by_indent`),
            // which all carry their own explicit `consumed_since` stall
            // guard instead of trusting their callee to always consume.
            // A future nullable `command` leading production (grammar
            // data can change; this loop's code should not have to)
            // would otherwise spin here forever re-matching the same
            // zero-width success at the same `pos` — exactly the
            // never-hang guarantee this crate exists to uphold. So:
            // treat a zero-width SUCCESS the same as a failure — discard
            // it and force resync via `recover_command` (always
            // consumes >= 1 token, or hits EOF). UNREACHABLE on the
            // current grammar (no `command` leading production is
            // nullable, so `ps.pos` always advances on `Ok`) — this arm
            // is dead code today by construction, confirmed by the
            // golden gate staying byte-exact with it present.
            Ok(()) if ps.pos == sp.pos => {
                ps.restore(&sp);
                ps.recover_command();
            }
            // M3b1 Task 7: a CLEAN command parse (this arm only — never
            // the recovery arms below, which restore to `sp` and so have
            // nothing of this command left to inspect) may itself have
            // been a `notation`/`mixfix` declaration. Materialize just
            // this command's subtree from its own event slice
            // (`ps.events[sp.events..]`, `sp` taken right before `run`
            // above — a `Category` call's events are always one balanced
            // subtree) via the same tested `flatten_events`/`build_tree`
            // infra `finish_into_tree` uses for the whole module, and
            // hand it to `derive` (Task 4). `derive` returns `None` for
            // every non-notation command shape (and, per its own doc
            // comment, for a malformed one too — its child-navigation is
            // `?`-propagated `Option` throughout), so this is a no-op on
            // every command that isn't a clean `notation`/`mixfix` —
            // exactly the "empty overlay never mutated" no-regression
            // bar the brief sets.
            //
            // `ps.merged_kinds()` (base + overlay-so-far), not the bare
            // base `ps.kinds`: a mixfix/notation command's OWN RHS can
            // itself use a notation this same loop registered on an
            // earlier command, so `derive`'s kind-name lookups need
            // every overlay kind registered before THIS command, not
            // just the immutable base set.
            //
            // Review follow-up (Issue 1, perf): the block below builds a
            // SECOND green subtree for this command (`finish_into_tree`
            // builds the whole module's tree, including this command,
            // again at the end) and, once any overlay kind exists,
            // clones the whole base interner via `merged_kinds` — for
            // EVERY command, even though `derive` can only ever return
            // `Some` for the two outer kinds `command_may_grow_grammar`
            // checks. Gate the build behind that cheap peek (follows the
            // single `Sub` marker to its subtree's root `Event::Start`
            // kind — no tree build) so a notation-free file pays none of
            // this per command, restoring the plain M3a hot path; a
            // `mixfix`/`notation` command still builds+derives+registers
            // exactly as before.
            Ok(()) if ps.command_may_grow_grammar(sp.events) => {
                let cmd_events = flatten_events(&ps.events[sp.events..], &ps.subtrees);
                let cmd_kinds = ps.merged_kinds();
                let subtree = build_tree(ps.src, &cmd_events, cmd_kinds);
                if let Some(spec) =
                    crate::grammar::notation::derive(&subtree.root(), &subtree.kinds)
                {
                    ps.overlay.register(spec);
                    // Grammar just changed: any `cat_cache` entry from
                    // before this command is memoized against the OLD
                    // grammar (Task 6's cache key has no dependency on
                    // overlay state) and would replay stale
                    // leading/trailing candidate sets if hit again.
                    ps.clear_category_cache();
                }
            }
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

/// Parse ONLY the module header and return the imported module names
/// (dotted), so a caller (the CLI) can resolve imports before the real
/// parse. Total: any input yields a (possibly empty) list, never a
/// panic. The header grammar is fixed (imports cannot themselves depend
/// on imports — the header cannot grow the grammar it's parsed with),
/// so the builtin snapshot is always sufficient — official Lean's own
/// `parseHeader` has the same property.
///
/// Lifts exactly `run_module`'s header phase (see there): `ps.start`
/// the synthetic `module` root, `ps.run` the snapshot's `header_prim`,
/// `ps.finish` the root, then `ps.finish_into_tree()` — the same
/// event-flattening/tree-build call `run_module` uses for the whole
/// module, just closed right after the header instead of after the
/// command loop + `eoi`. No worker thread (unlike `parse_module`): the
/// header's own grammar has no unbounded input-driven recursion (no
/// category can recurse into itself through an import line — imports
/// are `atomic(..) >> ident`, nothing nests), so `MIN_STACK_BYTES` is
/// not a concern here.
///
/// The one piece of new logic is the walk below: every
/// `Lean.Parser.Module.import` node's ident token(s), joined with `.`.
/// Normally the module name lexes as one dotted `Ident` token (Task 4
/// brief: "Foo.Bar.Baz is ONE ident token"); `ident_with_partial_trailing_dot`
/// (`builtin/command.rs`) can also split a trailing-dot edge case into
/// two `Ident` tokens around a `.` atom, so joining every `KIND_IDENT`
/// child found (in source order) reconstructs the full dotted name
/// either way.
pub fn parse_header_imports(src: &str) -> Vec<String> {
    let snap = crate::builtin::snapshot();
    let kinds = snap.kinds();
    let mut ps = Ps::new(src, &snap);
    let Some(module_kind) = kinds.lookup("module") else {
        // Unreachable on the real builtin snapshot (`builtin::snapshot`
        // always interns "module") — defensive only, so this stays
        // total even if that invariant is ever violated.
        return Vec::new();
    };
    ps.start(module_kind);
    if let Some(header) = snap.header_prim() {
        // Best-effort: a malformed header still leaves `ps` in a valid
        // (if partial/erroring) state — `run`'s own combinators never
        // panic on untrusted input, and any failure here just means a
        // smaller (possibly empty) partial tree to walk below.
        let _ = ps.run(&header);
    }
    ps.finish(); // module
    let (tree, _errors) = ps.finish_into_tree();

    let import_kind_name = "Lean.Parser.Module.import";
    let mut out = Vec::new();
    for node in tree.root().descendants() {
        if tree.kinds.name(node.kind()) != import_kind_name {
            continue;
        }
        let mut parts = Vec::new();
        for el in node.children_with_tokens() {
            if let rowan::NodeOrToken::Token(t) = el {
                if t.kind() == KIND_IDENT {
                    parts.push(t.text().to_string());
                }
            }
        }
        if !parts.is_empty() {
            out.push(parts.join("."));
        }
    }
    out
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
        // Same guarded message construction as every other furthest-failure
        // diagnostic (`push_furthest_error`) — reusing it (rather than
        // hand-rolling "expected one of: {join}" here again) is what keeps
        // this from ever emitting a dangling "expected one of: " when the
        // expected set is empty.
        self.push_furthest_error();
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

/// **Minimum-stack contract.** `leanr_syntax` parses untrusted input by
/// native recursion (`Ps::run` → `category` → `Ps::run` …), so it needs
/// a guaranteed amount of native stack to be able to promise "never
/// overflow" (Global Constraint: never panic / never fail to terminate,
/// on any input). This constant is that amount, and
/// `MAX_CATEGORY_DEPTH` is calibrated against it.
///
/// **It is not a precondition on callers.** `parse_module` runs the parse
/// on a worker thread it sizes itself (`stack_size(MIN_STACK_BYTES)` — see
/// there), so the guarantee is unconditional and internal. It was briefly
/// a documented caller obligation instead, which was a mistake: nothing
/// checked it, every default environment violates it (main thread 8 MiB;
/// a `tokio` worker or a `libtest` thread 2 MiB), and the failure mode was
/// a SIGSEGV — strictly worse than the panic the untrusted-input rule
/// forbids (Task 11b review wave 2, Critical 2). The constant stays public
/// because it is the number `MAX_CATEGORY_DEPTH` is derived from, and
/// because anything that calls *below* `parse_module` — this crate's own
/// deep-nesting unit tests drive `Ps::category` directly — still has to
/// supply it for itself.
///
/// Sized against the measured worst case rather than a guess (Task 11b
/// review, Critical 2 — the previous calibration was taken against
/// `libtest`'s 2 MiB default and so let a *harness* constraint dictate a
/// language limit). Method: nest the heaviest builtin shapes to depth D
/// on a thread of exactly S bytes and bisect the largest D that does not
/// overflow, then divide S by the `cat_depth` actually reached (not by
/// the visible nesting depth — a single `do { if p then do { … } }` level
/// costs ~3 `category()` calls). Worst measured cost per `cat_depth`
/// level, at S = 8 MiB:
///
/// | shape (`builtin/`)                | debug   | release |
/// |-----------------------------------|---------|---------|
/// | `do { if p then do { … } }`       | 23.0 KiB| 2.9 KiB |
/// | `do { … }` / `do { for … do { …}}`| 20.6 KiB| 2.7 KiB |
/// | `fun x => …`                      | 14.8 KiB| 2.7 KiB |
/// | `⟨…⟩`, `(…)`, `(… : T)`           | 11-13 KiB| 2.7 KiB|
///
/// So `MAX_CATEGORY_DEPTH` × 23.0 KiB = 5.6 MiB of the 16 MiB contract
/// in the *unoptimized* build (the expensive one) — a **2.8x margin**,
/// and ~21x in release. Re-bisect both numbers if a future grammar adds
/// a heavier production than nested `do`/`if`.
pub const MIN_STACK_BYTES: usize = 16 * 1024 * 1024;

/// Depth cap on input-driven `Category` recursion (nested parens and the
/// like — adversarial input can nest these arbitrarily, and `category`
/// recurses through `Ps::run` for every level). Together with
/// `MIN_STACK_BYTES` this is the parser's stack-safety contract: native
/// recursion only ever happens on a cache MISS (a hit costs no stack —
/// see `category`), and every miss is gated here, so the native depth of
/// a parse is bounded by this constant regardless of input.
///
/// **Not an oracle port** — and the pinned oracle is explicit about why
/// we need one anyway. In `v4.32.0-rc1`, `src/lean/Lean/Parser/` contains
/// NO recursion guard at all (no `maxRecDepth`, no `withIncRecDepth`, no
/// stack check): Lean's parser recurses until the *thread stack* runs
/// out, and then the process dies — measured on the pinned toolchain,
/// parse-only (`tests/fixtures/syntax/dump_syntax.lean`): `def a :=
/// ((…1…))` parses cleanly at 3,812 nested parens and at 3,952 prints
/// "Stack overflow detected. Aborting." (SIGABRT). Lean survives that in
/// practice by giving its worker threads a big, *explicitly sized* stack
/// (`lean -s/--tstack=<KB>`), which is precisely the `MIN_STACK_BYTES`
/// contract above. An abort is not an option for us (Global Constraint:
/// never panic on untrusted input), so we keep a deterministic cap; it is
/// this port's own device, not Lean's.
///
/// Chosen so that it cannot reject Lean that Lean itself accepts:
/// - Lean's own *language-level* recursion budget is `maxRecDepth`,
///   `defaultMaxRecDepth = 512` (`Init/Prelude.lean:4804`, enforced by
///   `Lean/Util/RecDepth.lean` in the ELABORATOR, not the parser). A term
///   nested past it is rejected by Lean with default options — measured:
///   512 nested parens ⇒ "maximum recursion depth has been reached".
/// - The deepest parse tree in ALL of pinned Mathlib (8,191 files, parsed
///   with Lean's own parser + Mathlib's parser tables) has node depth
///   **88** (`Mathlib/Tactic/GCongr/Core.lean`; mean per-file max 26).
///   Node depth upper-bounds the `cat_depth` a file needs, so 256 clears
///   the deepest real-world Lean command by ~3x.
///
/// The cap is deliberately a plain counter — no stack-pointer probing —
/// so that acceptance is *deterministic*: the same input parses the same
/// way in debug and release, which a "remaining stack headroom" guard
/// could not promise.
pub const MAX_CATEGORY_DEPTH: u32 = 256;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub code: &'static str,
    /// Byte span the error points at.
    pub span: (u32, u32),
    pub msg: String,
}

/// Render one `ParseError` as a `"line:col: error[Exxxx]: message"` line
/// (Task 13's CLI diagnostic renderer — task-11-brief.md Step 4). Lines
/// are 1-based; columns are 1-based CODEPOINT offsets (matching
/// `Ps::line_col`'s own convention, ORACLE-PORT `FileMap.toPosition`'s
/// `toColumn` — counts `Char`s, not bytes or UTF-16 units).
///
/// File-agnostic by design (no path parameter): the caller (the CLI)
/// prefixes whatever `path:` it likes; this crate has no notion of
/// "the current file" of its own (`parse_module` takes bare `&str`).
pub fn render_error(src: &str, e: &ParseError) -> String {
    let mut line = 1;
    let mut col = 1;
    for (i, c) in src.char_indices() {
        if i >= e.span.0 as usize {
            break;
        }
        if c == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    format!("{line}:{col}: error[{}]: {}", e.code, e.msg)
}

/// Parse failure marker; all context lives in `Ps` (furthest/expected).
#[derive(Debug)]
pub struct Fail;
pub type PResult = Result<(), Fail>;

/// A parse-time event: either a real tree `Event`, or a REFERENCE to a
/// whole `category()` subtree that has already been computed and lives in
/// `Ps::subtrees`.
///
/// This indirection is what makes the `category()` memo table (Task 11b)
/// cost O(total events) instead of O(`MAX_CATEGORY_DEPTH` × total events)
/// — see `Ps::subtrees` for the measurement and the argument. It is also
/// the shape the ORACLE has: Lean's `ParserCacheEntry.stx` is a `Syntax`
/// *node* (`Lean/Parser/Types.lean:256`) — a persistent, structurally
/// shared tree, so an outer cached node holds a POINTER to the inner
/// cached node rather than a copy of it. Storing flat event copies was
/// this port's divergence, and O(depth × n) retention was its price.
///
/// Never escapes the parser: `finish_into_tree` flattens the whole thing
/// back into a plain `Vec<Event>` (`flatten_events`), so `tree.rs` and the
/// public `Event` type are untouched by any of this.
#[derive(Clone, Debug)]
enum PEvent {
    Ev(Event),
    Sub(usize),
}

/// The error-stream twin of `PEvent` — same indirection, same reason: a
/// cached `category()` subtree's errors would otherwise be copied once per
/// enclosing cached call. (`Prim::Tactic`'s "unknown tactic" E0301 is a
/// diagnostic a *successful* category parse can emit, once per unknown
/// tactic, so this axis is adversarially reachable too — not just the
/// event axis.)
#[derive(Clone, Debug)]
enum PError {
    Err(ParseError),
    Sub(usize),
}

/// One memoized `category()` call's OWN output — the events and errors it
/// appended itself, with each nested `category()` call left as a `Sub`
/// reference rather than inlined. Owned by `Ps::subtrees`; referenced by
/// `CatOutcome::Ok`.
struct Subtree {
    events: Vec<PEvent>,
    errors: Vec<PError>,
    /// Is the LAST real `Event::Token` anywhere in this subtree trivia?
    /// `None` = the subtree contains no token at all (it is entirely
    /// structural — `Start`/`Finish`/`Missing`).
    ///
    /// Precomputed because `had_ws_before_current` (`Prim::CheckWsBefore`,
    /// the whitespace gate `Term.app`'s argument list depends on) answers
    /// exactly this question by scanning `Ps::events` backwards — and once
    /// a completed category call collapses to a single `PEvent::Sub`, the
    /// token it needs to see is no longer in `Ps::events` at all. Folding
    /// the answer in at construction keeps that scan O(1) per subtree
    /// instead of forcing it to re-descend.
    last_tok_trivia: Option<bool>,
}

/// Flatten a `PEvent` stream (expanding every `Sub` reference against
/// `subs`) into the plain `Event` stream `tree.rs` consumes.
///
/// Iterative, with an explicit worklist rather than native recursion: the
/// nesting is input-driven (bounded by `MAX_CATEGORY_DEPTH`, but the
/// untrusted-input rule says "never overflow", and a heap worklist makes
/// that unconditional rather than a second thing to calibrate).
/// Termination is structural: a `Sub(id)` can only ever be pushed by a
/// call that RETURNED before its parent captured it, so `id` is strictly
/// less than the id of any subtree referencing it — the reference graph is
/// a DAG ordered by construction, and cannot cycle.
fn flatten_events(root: &[PEvent], subs: &[Subtree]) -> Vec<Event> {
    let mut out = Vec::with_capacity(root.len());
    let mut stack: Vec<(&[PEvent], usize)> = vec![(root, 0)];
    while let Some(&(slice, i)) = stack.last() {
        if i >= slice.len() {
            stack.pop();
            continue;
        }
        stack.last_mut().expect("just peeked").1 += 1;
        match &slice[i] {
            PEvent::Ev(e) => out.push(e.clone()),
            PEvent::Sub(id) => stack.push((&subs[*id].events, 0)),
        }
    }
    out
}

/// `flatten_events`'s twin for the error stream. Order is preserved
/// exactly: a child's errors sit, contiguously, at the point in its
/// parent's error list where the child ran — which is precisely where its
/// `Sub` marker was pushed.
fn flatten_errors(root: &[PError], subs: &[Subtree]) -> Vec<ParseError> {
    let mut out = Vec::with_capacity(root.len());
    let mut stack: Vec<(&[PError], usize)> = vec![(root, 0)];
    while let Some(&(slice, i)) = stack.last() {
        if i >= slice.len() {
            stack.pop();
            continue;
        }
        stack.last_mut().expect("just peeked").1 += 1;
        match &slice[i] {
            PError::Err(e) => out.push(e.clone()),
            PError::Sub(id) => stack.push((&subs[*id].errors, 0)),
        }
    }
    out
}

/// The `last_tok_trivia` summary for a freshly built subtree (see that
/// field): the last real token in `events`, consulting an already-built
/// nested subtree's own summary rather than re-descending into it.
fn last_tok_trivia(events: &[PEvent], subs: &[Subtree]) -> Option<bool> {
    events.iter().rev().find_map(|e| match e {
        PEvent::Ev(Event::Token { kind, .. }) => Some(crate::kind::is_trivia(*kind)),
        PEvent::Ev(Event::Start(_) | Event::Finish | Event::Missing) => None,
        PEvent::Sub(id) => subs[*id].last_tok_trivia,
    })
}

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
    /// Same-file grammar growth (M3b1 Task 6): consulted AFTER the base
    /// snapshot at the three grammar read points (munch — `overlay.tokens()`
    /// in `peek_significant`/`peek_significant_readonly`/`bump`; dispatch —
    /// `category`'s leading/trailing candidate gathering; kind naming —
    /// `merged_kinds`, used by `finish_into_tree`). Starts empty
    /// (`Overlay::new(snap)`, `Ps::new`), so a `Ps` nobody calls
    /// `install_overlay` on behaves byte-identically to M3a at every one
    /// of those three points (empty token table ⇒ `munch_with` ≡ `munch`;
    /// `category_delta` always `None` ⇒ no candidates appended;
    /// `merged_kinds` short-circuits to a plain `Arc::clone` of the base
    /// interner — see each site's own doc comment).
    overlay: Overlay,
    events: Vec<PEvent>,
    errors: Vec<PError>,
    /// Append-only arena of memoized `category()` subtrees — the backing
    /// store `PEvent::Sub`/`PError::Sub` point into, and (via
    /// `CatOutcome::Ok`) what a cache hit replays.
    ///
    /// **Why the indirection exists** (Task 11b review wave 2,
    /// Important 1). The cache used to store, per entry, a flat COPY of
    /// the whole event slice the call produced. Since a category call's
    /// slice contains its children's slices, a token was retained once per
    /// enclosing cached call — O(`MAX_CATEGORY_DEPTH` × n), and the wave-1
    /// cap raise (40 → 256) multiplied it by 6.4x. Measured, before this
    /// change: 98 KiB of source nested just under the cap
    /// (`(`×252 around a large term) retained **325 MiB**; the cache held
    /// 10.5M events against 42K live ones, a 248x blowup that tracks the
    /// nesting depth exactly. Linear in file size, so a few-MiB adversarial
    /// file exhausts memory — the same resource-exhaustion DoS this task
    /// exists to close, in the memory axis instead of the time axis.
    ///
    /// A subtree now stores only its OWN events/errors, with each nested
    /// category call left as a `Sub` id, so each event is retained exactly
    /// once no matter how deeply it is nested: O(n), not O(cap × n). Same
    /// input, after: 1.9 MiB.
    ///
    /// **Why not eviction or a size threshold** (the other two candidates).
    /// Both re-open the Θ(3^depth) DoS. A size threshold ("don't cache
    /// slices bigger than T") declines to cache *precisely* the deeply
    /// nested subtrees — the ones whose siblings must hit — so the
    /// `paren`/`tuple`/`typeAscription` fanout re-parses them and the blowup
    /// returns. Eviction is worse than it looks: the memo table's
    /// polynomial bound needs an entry computed inside a call to survive
    /// until that call returns, and "survive until the IMMEDIATE parent
    /// returns" is NOT enough — a key reached from two different children of
    /// the same parent would be recomputed under each, which is exactly the
    /// branching that gives 3^depth back. Nothing short of "never evict
    /// within one `parse_module`" preserves the bound, so the fix has to be
    /// in the REPRESENTATION, not the retention policy. Which is also where
    /// the oracle put it: `ParserCacheEntry.stx` is a shared `Syntax` node,
    /// not a copy (see `PEvent`).
    subtrees: Vec<Subtree>,
    furthest_pos: usize,
    furthest_expected: Vec<String>,
    /// Current right-binding power: `Category` sets it on recursion,
    /// `Node`'s `prec` gate reads it.
    prec: u32,
    /// Precedence of the last completed leading/trailing node.
    lhs_prec: u32,
    /// `withPosition` stack: saved (line, col) of a position marker.
    pos_stack: Vec<(u32, u32)>,
    /// ORACLE-PORT `Basic.lean`'s `forbiddenTk?` parser-context field —
    /// `withForbidden`/`withoutForbidden`'s scope stack (Task 9: the
    /// FIRST real user — `doForDecl`'s iterable, `doIfCond`'s
    /// condition, `doUnless`/`termUnless`'s condition, `doFor`/
    /// `termFor`'s per-declaration iterable all wrap `termParser` in
    /// `withForbidden "do" ..` to stop the term Pratt-loop from
    /// swallowing the construct's OWN trailing `"do "` keyword as an
    /// application argument — Term.do's own precedence, `argPrec`,
    /// is exactly `ARG_PREC`, so without this it WOULD qualify as an
    /// `argument()`-strength trailing argument and get eaten, per
    /// `mkTokenAndFixPos` (Basic.lean): "if a token *anywhere* in `p`
    /// resolves to the forbidden text, parsing stops there — Task 9
    /// verified this is not just theoretical: an early version of
    /// `doFor`'s port without this hard-failed on `for x in xs do ..`
    /// (see task-9 report for the probe/regression test). A `Vec`
    /// stack (not one `Option`) mirrors `pos_stack`'s own
    /// save/restore-on-exit discipline for correctly-nested scopes
    /// (`withForbidden` inside `withForbidden`, or `withoutForbidden`
    /// nested inside one — e.g. a parenthesized term used as a `for`
    /// loop's iterable).
    forbidden_stack: Vec<Option<String>>,
    /// Byte offset of each line start (for column computation).
    line_starts: Vec<usize>,
    /// Input-driven `Category` recursion depth — see
    /// `MAX_CATEGORY_DEPTH`.
    cat_depth: u32,
    /// `category()` memoization table (Task 11b — untrusted-input
    /// never-hang hardening). ORACLE-PORT `ParserCache`/
    /// `ParserCacheKey`/`withCacheFn` (`Lean/Parser/Types.lean`) and
    /// `categoryParser` (`Basic.lean:1736`), which wraps EVERY
    /// category-parse in exactly this cache. See `category`'s doc
    /// comment for the full citation, the key/entry shapes
    /// (`CatCacheKey`/`CatCacheEntry`), and the correctness argument.
    cat_cache: HashMap<CatCacheKey, CatCacheEntry>,
    /// Per-open-`category()`-call furthest-failure tally, pushed on
    /// entry and popped on exit (stack discipline mirrors `pos_stack`/
    /// `forbidden_stack`) — lets a cache HIT replay its exact effect on
    /// the global furthest-failure tracker (`furthest_pos`/
    /// `furthest_expected`) and on every still-open ancestor's own
    /// eventual cache entry, without re-running any parser code. `None`
    /// = nothing recorded yet in this call's dynamic extent. See
    /// `category`'s doc comment (the "Correctness" section) for why a
    /// plain snapshot-and-replay of the GLOBAL tally would be unsound.
    furthest_stack: Vec<Option<(usize, Vec<String>)>>,
    /// How many times this parse has produced a depth-cap artifact — a
    /// monotone counter, never reset, bumped both by the
    /// `MAX_CATEGORY_DEPTH` arm itself AND by a cache hit that REPLAYS a
    /// depth-tainted (`depth_headroom: Some(_)`) entry, since inheriting
    /// an artifact taints a call exactly as much as producing one does
    /// (Task 11b review wave 2, Critical 1). `category` reads it on entry
    /// and again on exit: if it moved, the depth cap shaped something
    /// inside THAT call's dynamic extent, so the call's result is a
    /// function of the depth budget it had and not of its cache key
    /// alone, and it is filed under `depth_headroom: Some(headroom)`
    /// rather than the depth-independent `None` bucket (see `category`'s
    /// doc comment, "`cat_depth` and the cache"). O(1), no parallel stack
    /// needed: category calls nest, so a bump inside a child is by
    /// construction inside every open ancestor too, and each open call
    /// holds its own `cap_hits`-on-entry value in its own native frame.
    cap_hits: u64,
    /// Quotation nesting depth — ORACLE-PORT `CacheableParserContext.
    /// quotDepth` (`incQuotDepth`/`decQuotDepth`, `Basic.lean`). `0`
    /// outside any quotation; `Term.quot`/`Tactic.quot`/`Command.quot`/
    /// `Term.dynamicQuot` each bump it by 1 around their body (M3b2b
    /// Task 2). NOT in `Savepoint`: every increment/decrement pairs
    /// inside a single `run()` frame (`Prim::IncQuotDepth`/
    /// `DecQuotDepth`'s arms save-and-restore around their inner `run`
    /// call, exactly like `forbidden_stack`/`pos_stack`'s own push/pop
    /// discipline), so backtracking can never leak a stale depth — a
    /// failed alternative's `restore()` unwinds `events`/`errors`/`pos`,
    /// but by the time that `restore()` runs, the `IncQuotDepth` arm
    /// that opened this scope has ALREADY decremented back on its own
    /// stack frame's way out (Rust's own call-stack unwind undoes it,
    /// same argument as the other two stacks). Reading nothing here
    /// used to be exact for M3a/M3b1 (no quotation machinery existed —
    /// see `CatCacheKey`'s doc comment, since updated); Task 3 is what
    /// makes something (antiquotation alternatives) actually READ this
    /// field — here it is only ever set.
    quot_depth: u32,
}

/// Memoization key for `category()`. ORACLE-PORT `ParserCacheKey`
/// (`Lean/Parser/Types.lean:247`): `CacheableParserContext`'s `prec`,
/// `savedPos?`, `forbiddenTk?` fields plus `parserName`/`pos`.
/// `CacheableParserContext` also has `suppressInsideQuot` — a
/// bootstrapping-only field (`adaptCacheableContext` calls in
/// `Basic.lean` around macro antiquotation support) this crate never
/// sets or reads (`ORACLE-PORT` divergence, not an oversight: always
/// constant here, so omitting it from the key partitions the cache
/// identically to including an always-equal field would). `quotDepth`,
/// its sibling, WAS in that same "never set or read" bucket through
/// M3a/M3b1 but is real, cache-relevant state as of M3b2b Task 2 (see
/// `Ps::quot_depth`'s doc comment) — hence `quot_depth` below, keyed in
/// for the same reason `forbidden`/`saved_pos` are: a term memoized at
/// depth 0 must never satisfy a depth-1 lookup once Task 3's
/// antiquotation alternatives make the two observably different.
/// `name` is `parserName`; `rbp` is `prec` (`categoryParser` sets
/// `c.prec := prec` via `adaptCacheableContextFn` immediately before
/// consulting the cache — Basic.lean:1736-1737 — so this fn's own
/// `rbp` argument IS that `prec` field, no separate tracking needed);
/// `forbidden`/`saved_pos` are `forbiddenTk?`/`savedPos?`, read off
/// `Ps::forbidden()`/`pos_stack.last()` — this port's un-opaque
/// equivalents of `withForbidden`/`withPosition`'s
/// `adaptCacheableContext` writes (see those `Prim` arms' own doc
/// comments). Owned `String`s (not borrowed `&str`) because the
/// `Prim::Category { name, .. }` a given call reads from may itself
/// live in a short-lived clone (`longest_match`'s per-candidate
/// `Vec<Prim>`), not in anything with `Ps`'s own `'a` snapshot
/// lifetime — cloning a handful of short strings per category call is
/// cheap next to the exponential blowup this cache removes.
///
/// `depth_headroom` has no oracle counterpart (Lean's parser has no
/// recursion budget at all — see `MAX_CATEGORY_DEPTH`): it is this
/// port's own device for keeping `cat_depth`, which IS ambient state a
/// result can depend on, out of the cache's blind spot. Task 11b review,
/// Critical 1 — see `category`'s doc comment, "`cat_depth` and the
/// cache".
#[derive(Clone, PartialEq, Eq, Hash)]
struct CatCacheKey {
    pos: usize,
    name: String,
    rbp: u32,
    forbidden: Option<String>,
    saved_pos: Option<(u32, u32)>,
    /// `None` = this result is depth-INDEPENDENT (the `MAX_CATEGORY_DEPTH`
    /// cap never fired anywhere inside the call that produced it), so it
    /// is valid to replay at any `cat_depth`. `Some(h)` = the cap DID fire
    /// inside, so the result is an artifact of having had exactly `h`
    /// levels of budget left, and may only be replayed at that same
    /// headroom.
    depth_headroom: Option<u32>,
    /// `Ps::quot_depth` at call time — ORACLE `CacheableParserContext.
    /// quotDepth` (M3b2b Task 2; see this struct's own doc comment).
    /// Antiquotation alternatives (Task 3) read `quot_depth`, so a term
    /// memoized at depth 0 (outside any quotation) must be a cache MISS
    /// against a depth-1 lookup (inside one) even at the identical
    /// `pos`/`rbp`/`forbidden`/`saved_pos` — same reasoning as every
    /// other field here, just for a piece of ambient state this task
    /// introduces rather than one M3a already had.
    quot_depth: u32,
}

/// What a `category()` call replays on a cache hit. ORACLE-PORT
/// `ParserCacheEntry` (`stx`, `lhsPrec`, `newPos`, `errorMsg`,
/// `Types.lean:256`): `sub` is our `stx` — an id into `Ps::subtrees`,
/// which (like Lean's `Syntax`) is a structurally SHARED node, not a copy
/// (wave 2, Important 1 — see `PEvent`/`Ps::subtrees`). We additionally
/// have a genuine FAILURE case (`CatOutcome::Err`) real Lean's one
/// entry shape doesn't need: Lean's parsers always "succeed" at the
/// stack-effect level (a failed alternative still pushes `missing`
/// plus sets `errorMsg`), so one shape covers both; this port's
/// `Result`-based backtracking has two genuinely different shapes — a
/// failed `category()` call restores to its own entry savepoint and so
/// has no events/errors of its own to replay, only a furthest-failure
/// effect.
#[derive(Clone)]
struct CatCacheEntry {
    outcome: CatOutcome,
    /// This port's own addition — see `Ps::furthest_stack`'s doc
    /// comment. No oracle counterpart: Lean has no cross-attempt
    /// "furthest failure" tally to keep sound under caching.
    furthest: Option<(usize, Vec<String>)>,
}

#[derive(Clone)]
enum CatOutcome {
    Ok {
        /// Index into `Ps::subtrees` — replaying this entry is a single
        /// `PEvent::Sub(sub)` push, O(1), no matter how big the subtree.
        sub: usize,
        end: usize,
        lhs_prec: u32,
    },
    Err,
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
    events: Vec<PEvent>,
    errors: Vec<PError>,
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
            overlay: Overlay::new(snap),
            events: Vec::new(),
            errors: Vec::new(),
            furthest_pos: 0,
            furthest_expected: Vec::new(),
            prec: 0,
            lhs_prec: 0,
            pos_stack: Vec::new(),
            forbidden_stack: Vec::new(),
            line_starts,
            cat_depth: 0,
            cat_cache: HashMap::new(),
            subtrees: Vec::new(),
            furthest_stack: Vec::new(),
            cap_hits: 0,
            quot_depth: 0,
        }
    }

    /// Current forbidden-token scope, if any — ORACLE-PORT
    /// `ParserContext.forbiddenTk?` (the top of `forbidden_stack`, or
    /// none outside any `withForbidden` scope).
    fn forbidden(&self) -> Option<&str> {
        self.forbidden_stack.last().and_then(|o| o.as_deref())
    }

    fn table(&self) -> &TokenTable {
        &self.snap.tokens
    }

    /// Install a same-file grammar overlay (M3b1 Task 6): from this call
    /// on, the three grammar read points consult it (see the `overlay`
    /// field's own doc comment). `pub(crate)` — used by this file's own
    /// test below, and, from Task 7, the command loop that grows the
    /// overlay mid-parse as `notation`/mixfix commands are seen.
    pub(crate) fn install_overlay(&mut self, ov: Overlay) {
        self.overlay = ov;
    }

    /// Empty `cat_cache` (Task 11b's `category()` memoization table —
    /// see its own doc comment). Called from the command loop (Task 7)
    /// right after `self.overlay.register(..)` grows the grammar
    /// mid-file: `CatCacheKey` has no dependency on overlay state (it
    /// keys purely on `pos`/`name`/`rbp`/`forbidden`/`saved_pos`/
    /// `depth_headroom` — see that struct's doc comment), so a stale
    /// entry computed under the PRE-registration grammar (e.g. "no
    /// leading production matched at this `pos`" for a category the new
    /// notation just added a production to) would otherwise replay as a
    /// cache HIT against the post-registration grammar and silently
    /// resurrect exactly the bug this task closes. Cheap and correct
    /// over "invalidate just the affected category": entries are
    /// bounded by this SAME command's own work (each command starts
    /// this call from an empty-at-command-start cache in practice, since
    /// nothing outside `category()` itself populates it and the loop
    /// clears it after every notation-registering command), and grammar
    /// growth is bounded by command count, not token count (this call
    /// site fires at most once per command, never per token).
    pub(crate) fn clear_category_cache(&mut self) {
        self.cat_cache.clear();
    }

    /// M3b1 Task 7 review follow-up (Issue 1, perf): cheap peek — is the
    /// command whose event slice starts at `from_event`
    /// (`self.events[from_event..]`, a savepoint taken right before a
    /// SUCCESSFUL top-level `Category { name: "command", .. }` call — see
    /// `run_module`'s clean `Ok(())` arm) possibly a `notation`/`mixfix`
    /// declaration, i.e. worth paying `flatten_events` +
    /// `build_tree` + `derive` for at all?
    ///
    /// A successful `category()` call's own top-level footprint is
    /// ALWAYS exactly one `PEvent::Sub(idx)` marker — its Ok arm moves
    /// everything the call produced into `self.subtrees[idx]` and
    /// leaves only that one marker behind in the caller's event stream
    /// (see `category`'s Ok arm) — so resolving the outer kind never
    /// needs to build anything: follow the marker to its subtree, skip
    /// that subtree's own leading trivia (raw `Event::Token` events
    /// `category`'s pre-dispatch `peek_significant` emits directly,
    /// ahead of the winning leading candidate's own events), and read
    /// the `SyntaxKind` straight off the first `Event::Start` — which
    /// IS the whole command's outer node, because every `command`
    /// leading production is `nd(kind, ..)` (`Prim::Node`,
    /// `builtin/command.rs`'s shared helper), never a bare token/leaf.
    /// If the first non-trivia event isn't a `Start` (defensive only —
    /// unreachable on this crate's grammar, since no `command` leading
    /// production is a bare leaf), this conservatively reports
    /// "not eligible" rather than guessing.
    ///
    /// `derive` (`grammar/notation.rs`) returns `Some` ONLY for
    /// `Lean.Parser.Command.mixfix`/`Lean.Parser.Command.notation` —
    /// every other outer kind is an immediate `None` — so this peek's
    /// two-name check is exactly `derive`'s own outer-kind dispatch,
    /// evaluated without paying for a green tree first. Both names are
    /// BASE kinds (`command.rs`'s `mixfix`/`notation` are builtin
    /// productions, never overlay-registered), so the base `self.kinds`
    /// — not `merged_kinds()` — is enough here; no `Arc<KindInterner>`
    /// clone needed just to peek.
    pub(crate) fn command_may_grow_grammar(&self, from_event: usize) -> bool {
        let Some(&sub) = self.events[from_event..].iter().find_map(|e| match e {
            PEvent::Sub(idx) => Some(idx),
            PEvent::Ev(_) => None,
        }) else {
            return false;
        };
        let first_non_trivia = self.subtrees[sub].events.iter().find(|e| {
            !matches!(e, PEvent::Ev(Event::Token { kind, .. }) if crate::kind::is_trivia(*kind))
        });
        let Some(PEvent::Ev(Event::Start(kind))) = first_non_trivia else {
            return false;
        };
        let kind = *kind;
        let name = self.kinds.name(kind);
        name == "Lean.Parser.Command.mixfix" || name == "Lean.Parser.Command.notation"
    }

    /// Base kinds + this `Ps`'s overlay's own kinds, folded into ONE
    /// `KindInterner` — what `finish_into_tree` hands to `build_tree` so
    /// the final tree can name EVERY kind a `Prim::Node`/`TrailingNode`
    /// might have emitted. An overlay-numbered kind (`>= snap.kind_count()`
    /// — Task 5) is never in the base interner on its own, so resolving it
    /// at build time needs this; the events themselves are unchanged
    /// (`Prim::Node`'s kind u16 is already overlay-numbered when it's
    /// emitted — Task 5 — only NAME RESOLUTION at build time is new here).
    ///
    /// Correct because `KindInterner::intern` is append-only and
    /// idempotent (kind.rs): starting from a clone of exactly the base
    /// interner (`snap.kind_count()` entries — the same count
    /// `Overlay::new` recorded as `base_kind_count`) and re-interning the
    /// overlay's kind names in REGISTRATION order hands back exactly the
    /// ids `Overlay::intern` itself assigned (`base_kind_count + i`), so a
    /// `Prim::Node`'s overlay-numbered kind resolves to the same name
    /// either way.
    ///
    /// Empty overlay ⇒ `self.kinds.clone()`, a plain `Arc` bump — no new
    /// interner, no divergence from M3a's `finish_into_tree`, which did
    /// exactly that. Checked on `kind_names` directly (not
    /// `Overlay::is_empty`, which also looks at `cats`) since that is the
    /// exact condition under which the loop below would do nothing.
    fn merged_kinds(&self) -> Arc<KindInterner> {
        let names = self.overlay.kind_names();
        if names.is_empty() {
            return self.kinds.clone();
        }
        let mut merged = (*self.kinds).clone();
        for name in names {
            merged.intern(name);
        }
        Arc::new(merged)
    }

    fn snap_category(&self, name: &str) -> Option<&'a Category> {
        self.snap.categories.get(name)
    }

    // ---- events ----------------------------------------------------
    pub(crate) fn start(&mut self, kind: SyntaxKind) {
        self.events.push(PEvent::Ev(Event::Start(kind)));
    }
    pub(crate) fn finish(&mut self) {
        self.events.push(PEvent::Ev(Event::Finish));
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
            let (t, err) = next_token(self.src, self.pos, self.table(), self.overlay.tokens());
            let trivia = matches!(
                t.kind,
                TokenKind::Whitespace | TokenKind::LineComment | TokenKind::BlockComment
            );
            if !trivia {
                return (t, self.pos);
            }
            if let Some(e) = err {
                self.errors.push(PError::Err(ParseError {
                    code: e.code,
                    span: (self.pos as u32, (self.pos + t.len as usize) as u32),
                    msg: e.msg,
                }));
            }
            self.emit_token(trivia_kind(t.kind), t.len);
        }
    }

    /// Read-only preview of the next significant token's (kind, start
    /// offset) — unlike `peek_significant`, this NEVER mutates
    /// `self.pos`/`self.events`/`self.errors`: it scans forward from a
    /// local cursor only. ORACLE-PORT `checkColGtFn`/`checkWsBeforeFn`
    /// et al. (Basic.lean): every one of these check-combinators is a
    /// true `epsilonInfo` (zero-width, arity-0) parser that reads
    /// already-current position/trivia info (`s.pos`'s line/col, or the
    /// PREVIOUS syntax node's already-attached trailing-trivia span) —
    /// it never itself re-tokenizes forward. That works for the oracle
    /// because real Lean's tokenizer eagerly attaches trailing trivia
    /// to whatever token precedes (every consumed token "owns" the
    /// whitespace/comments up to the next one). THIS port's trivia is
    /// lazily discovered instead — only emitted when something
    /// genuinely commits to peeking forward (an upcoming leading/
    /// trailing dispatch, or a bump) — Task 5/6's deliberate,
    /// documented architecture. A check-combinator that used the
    /// COMMITTING `peek_significant` here would itself become a
    /// (partial) tokenizer pass; if whatever runs immediately after it
    /// then fails to consume anything further, that already-committed
    /// trivia-skip is indistinguishable from real progress to an
    /// enclosing `many`/`many1`'s `consumed_since` check — turning a
    /// clean, non-consuming stop into a hard, unrecoverable error
    /// (Task 8 wave 2 review fix: found via `Term.pipeProj`'s `many
    /// argument` — see `check_col`/`had_ws_before_current`'s callers
    /// and the regression test in this file's test module).
    fn peek_significant_readonly(&self) -> (Token, usize) {
        let mut pos = self.pos;
        loop {
            let (t, _err) = next_token(self.src, pos, self.table(), self.overlay.tokens());
            let trivia = matches!(
                t.kind,
                TokenKind::Whitespace | TokenKind::LineComment | TokenKind::BlockComment
            );
            if !trivia {
                return (t, pos);
            }
            pos += t.len as usize;
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
        self.events.push(PEvent::Ev(Event::Token {
            kind,
            offset: self.pos as u32,
            len,
        }));
        self.pos += len as usize;
    }

    /// Consume the peeked significant token as leaf `kind`.
    fn bump(&mut self, t: Token, kind: SyntaxKind) {
        if let (_, Some(e)) = next_token(self.src, self.pos, self.table(), self.overlay.tokens()) {
            self.errors.push(PError::Err(ParseError {
                code: e.code,
                span: (self.pos as u32, (self.pos + t.len as usize) as u32),
                msg: e.msg,
            }));
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
        // Task 11b: also fold this point into every currently-open
        // `category()` call's own LOCAL tally (independent of the
        // ambient `furthest_pos` above) — see `Ps::furthest_stack`'s
        // doc comment for why a plain snapshot-and-replay of the
        // global tally would be unsound once category calls cache.
        for local in &mut self.furthest_stack {
            Self::merge_furthest_point(local, at, what);
        }
        Fail
    }

    /// Fold one furthest-failure point into a LOCAL (call-scoped) tally
    /// — the same max-then-union rule `fail_expecting` applies to the
    /// global tally, applied instead to a tally that starts from
    /// nothing (`None`) rather than from whatever the ambient global
    /// tally happened to hold. This independence from the ambient
    /// starting value is exactly what makes the recorded summary safe
    /// to replay later against a DIFFERENT ambient value (see
    /// `category`'s "Correctness" doc section).
    fn merge_furthest_point(local: &mut Option<(usize, Vec<String>)>, at: usize, what: &str) {
        match local {
            None => *local = Some((at, vec![what.to_string()])),
            Some((pos, expected)) => {
                if at > *pos {
                    *pos = at;
                    *expected = vec![what.to_string()];
                } else if at == *pos {
                    let w = what.to_string();
                    if !expected.contains(&w) {
                        expected.push(w);
                    }
                }
            }
        }
    }

    /// Fold an already-computed summary (e.g. a cached child
    /// `category()` call's own tally) into a local tally — same rule
    /// as `merge_furthest_point`, generalized from one point to a
    /// (position, expected-set) pair.
    fn merge_furthest_summary(
        local: &mut Option<(usize, Vec<String>)>,
        other: &Option<(usize, Vec<String>)>,
    ) {
        let Some((at, expected)) = other else {
            return;
        };
        match local {
            None => *local = Some((*at, expected.clone())),
            Some((pos, exp)) => {
                if *at > *pos {
                    *pos = *at;
                    *exp = expected.clone();
                } else if *at == *pos {
                    for w in expected {
                        if !exp.contains(w) {
                            exp.push(w.clone());
                        }
                    }
                }
            }
        }
    }

    /// Replay a cached `category()` call's furthest-failure effect on
    /// both the real global tally (`furthest_pos`/`furthest_expected`)
    /// and every currently-open ancestor `category()` call's own local
    /// tally, reproducing exactly what a fresh (uncached) re-run of
    /// that call's body would have done to both — see `category`'s
    /// "Correctness" doc section.
    fn apply_furthest_summary(&mut self, summary: &Option<(usize, Vec<String>)>) {
        let Some((at, expected)) = summary else {
            return;
        };
        if *at > self.furthest_pos {
            self.furthest_pos = *at;
            self.furthest_expected = expected.clone();
        } else if *at == self.furthest_pos {
            for w in expected {
                if !self.furthest_expected.contains(w) {
                    self.furthest_expected.push(w.clone());
                }
            }
        }
        for local in &mut self.furthest_stack {
            Self::merge_furthest_summary(local, summary);
        }
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
        self.errors.push(PError::Err(ParseError {
            code: "E0301",
            span: (self.furthest_pos as u32, self.furthest_pos as u32),
            msg,
        }));
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
                self.events.push(PEvent::Ev(Event::Missing));
                Ok(())
            }
            Prim::EmitEmptyIdent => {
                // ORACLE-PORT `hygieneInfoFn`: always succeeds, emitting
                // a zero-width `ident` at the CURRENT position — no
                // `peek_significant` call, so no trivia is skipped
                // first (see the `Prim::EmitEmptyIdent` doc comment).
                self.events.push(PEvent::Ev(Event::Token {
                    kind: KIND_IDENT,
                    offset: self.pos as u32,
                    len: 0,
                }));
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
            Prim::UnknownTacticIdent => {
                // ORACLE-PORT `Tactic.«unknown» := leading_parser
                // withPosition (ident >> errorAtSavedPos "unknown
                // tactic" true)` (Tactic.lean:29). By the time this arm
                // runs, `self.pos` is already exactly the ident's start
                // byte offset: the enclosing `Category` dispatch's
                // leading-token lookahead is the COMMITTING
                // `peek_significant` (see `category`'s own doc
                // comment), so any leading trivia is already skipped/
                // emitted before ANY leading candidate — including this
                // one — is even tried. That's the same position
                // `withPosition` would mark here, so capturing
                // `self.pos` now stands in for the oracle's saved
                // marker without needing a separate byte-offset stack.
                let at = self.pos;
                self.run(&Prim::Ident)?;
                // `errorAtSavedPos`'s `mkUnexpectedErrorAt` calls
                // `mkUnexpectedError` with its default `pushMissing :=
                // true`, which pushes an ADDITIONAL `.missing` syntax
                // node on top of whatever `ident` already pushed — not
                // instead of it. `EmitMissing` is this crate's port of
                // that exact "always-succeeding, pushes a missing leaf"
                // shape (see its own doc comment).
                self.run(&Prim::EmitMissing)?;
                // DIVERGENCES from the oracle's literal `errorAtSavedPos
                // msg true` (Task 9 review finding 2 — documented here
                // per the finding's own instruction to record any
                // divergence at the code site):
                // 1. Position: real Lean reports at `c.next savedPos`
                //    (one char PAST the marker — `delta := true` exists
                //    purely to guarantee the report lands past a
                //    possibly-zero-width preceding parser). `ident` is
                //    never zero-width, so reporting at the marker
                //    itself (`at`, captured above) rather than marker+1
                //    char is an intentional, harmless simplification.
                // 2. No position rewind: `mkUnexpectedErrorAt` also
                //    resets `s.pos` BACK to the saved position before
                //    erroring (`s.setPos pos |>.mkUnexpectedError msg`)
                //    — real Lean's recovery machinery can rely on that
                //    backward jump because an enclosing `<|>`/longest-
                //    match may still try a DIFFERENT alternative from
                //    there. This port's `self.pos` must stay
                //    monotonically forward (every combinator's
                //    never-hang invariant depends on it — see
                //    `sep_by_indent`'s own zero-width guard, this same
                //    review wave's finding 1) and there is no other
                //    tactic-category alternative left to try anyway
                //    (`unknown` is already the MAX_PREC catch-all last
                //    resort), so skipping the rewind changes no
                //    observable outcome here: the ident's full span
                //    stays consumed, exactly as any OTHER successful
                //    tactic-category production would leave it.
                // 3. Failure vs. diagnostic: the oracle's `errorMsg`
                //    being set ultimately surfaces as a genuine
                //    parser-level error message ("error: unknown
                //    tactic", confirmed against a fresh oracle dump —
                //    see `builtin/tactic.rs`'s module doc comment)
                //    because nothing else in the category can then
                //    succeed. This port instead records the SAME
                //    message as a `ParseError` VALUE (this crate's
                //    whole error-handling architecture — `errors:
                //    Vec<ParseError>`, never a bare "the parse just
                //    failed") while the production itself still
                //    succeeds, producing a real (error-annotated) tree
                //    instead of no tree at all.
                self.errors.push(PError::Err(ParseError {
                    code: "E0301",
                    span: (at as u32, at as u32),
                    msg: "unknown tactic".to_string(),
                }));
                Ok(())
            }
            Prim::DocCommentBody => self.doc_comment_body(),
            Prim::IncQuotDepth(q) => {
                self.quot_depth += 1;
                let r = self.run(q);
                self.quot_depth -= 1;
                r
            }
            Prim::DecQuotDepth(q) => {
                let saved = self.quot_depth;
                self.quot_depth = saved.saturating_sub(1);
                let r = self.run(q);
                self.quot_depth = saved;
                r
            }
            Prim::DynamicQuotBody => self.dynamic_quot_body(),
            Prim::Many1Unbox(q) => self.many1_unbox_impl(q),
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
                // Task 8 wave 2 review fix: this marker-establishing
                // lookahead uses the READ-ONLY preview, not the
                // committing `peek_significant` — establishing WHERE the
                // marker sits doesn't need to consume anything, and
                // committing here would leak as phantom "consumption"
                // to an enclosing `many`/`many1` if `q` itself later
                // fails without independently consuming further (same
                // hazard as `check_col`/`had_ws_before_current`, see
                // `peek_significant_readonly`'s doc comment).
                let (_, at) = self.peek_significant_readonly();
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
                // `had_ws_before_current` is read-only (Task 8 wave 2
                // review fix — see its doc comment and
                // `peek_significant_readonly`'s), so neither arm here
                // needs its own save/restore any more: nothing to undo.
                if self.had_ws_before_current() {
                    Ok(())
                } else {
                    let at = self.pos;
                    Err(self.fail_expecting("<whitespace>", at))
                }
            }
            Prim::CheckNoWsBefore => {
                if self.had_ws_before_current() {
                    let at = self.pos;
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
            Prim::SepByIndent { item, sep, min } => self.sep_by_indent(item, sep, *min),
            Prim::WithForbidden(tok, q) => {
                // ORACLE-PORT `withForbidden`/`adaptCacheableContext`
                // (Basic.lean): scopes `forbiddenTk?` for the duration of
                // `q` only — restored (success or failure alike) once
                // `q` returns, same discipline as `WithPosition`'s
                // marker stack.
                self.forbidden_stack.push(Some(tok.clone()));
                let r = self.run(q);
                self.forbidden_stack.pop();
                r
            }
            Prim::WithoutForbidden(q) => {
                // ORACLE-PORT `withoutForbidden`: locally clears the
                // scope (e.g. a parenthesized sub-term has no parsing
                // ambiguity to guard against) rather than removing the
                // stack frame outright — an ENCLOSING `withForbidden`
                // must still apply once `q` returns.
                self.forbidden_stack.push(None);
                let r = self.run(q);
                self.forbidden_stack.pop();
                r
            }
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
        // ORACLE-PORT `mkTokenAndFixPos` (Basic.lean): "if
        // `c.forbiddenTk? == some tk`, [fail] 'forbidden token'" —
        // checked at the SAME granularity real Lean does it (per
        // literal-token match attempt), so a token that would otherwise
        // match is instead treated as a clean failure while a
        // `withForbidden` scope for that exact text is active. See
        // `Prim::WithForbidden`'s doc comment for why this matters
        // (`doFor`/`doUnless`/etc.'s iterable/condition must NOT let
        // `Term.app`'s argument loop swallow the construct's own
        // trailing `"do "` keyword).
        let ok = ok && self.forbidden() != Some(s);
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

    /// `Prim::DocCommentBody` — ORACLE-PORT `commentBody`'s `rawFn
    /// (finishCommentBlock (pushMissingOnError := true) 1)` (see the
    /// `Prim` variant's own doc comment for the full citation + a fresh
    /// oracle dump's exact span numbers). `peek_significant` performs the
    /// SAME leading-trivia skip every other leaf token gets (the oracle's
    /// own `>>` sequencing between `"/--"` and `commentBody` does this
    /// implicitly); the doc-comment text itself is then a raw,
    /// non-tokenizing scan (never calls `next_token` again — the body can
    /// contain arbitrary text, including sequences that wouldn't
    /// otherwise lex as valid Lean tokens) up through the matching,
    /// nesting-aware `-/`. A bare `emit_token` (no `start`/`finish`
    /// wrap) — `commentBody` is a plain `Parser`, not a `leading_parser`,
    /// so it contributes ONE leaf, never a node of its own (same
    /// "unwrapped leaf" shape as `Ident`/`Prim::FieldIdx`'s inner digits).
    fn doc_comment_body(&mut self) -> PResult {
        let (_, at) = self.peek_significant();
        match crate::lex::doc_comment_body_end(&self.src[at..]) {
            Some(len) => {
                self.emit_token(KIND_ATOM, len as u32);
                Ok(())
            }
            None => {
                // Unterminated doc comment: never hang/panic — consume
                // to EOF (matching `finishCommentBlock`'s own degraded
                // "ran off the end" fallback) and record a diagnostic
                // instead of failing the whole parse, this crate's
                // established "parse errors are values" architecture
                // (same E0303 code `block_comment_end`'s own unterminated
                // case already uses for the analogous plain-comment
                // case).
                let len = self.src.len() - at;
                self.errors.push(PError::Err(ParseError {
                    code: "E0303",
                    span: (at as u32, self.src.len() as u32),
                    msg: "unterminated comment".to_string(),
                }));
                self.emit_token(KIND_ATOM, len as u32);
                Ok(())
            }
        }
    }

    /// ORACLE `Term.dynamicQuot`'s `ident >> "| " >> incQuotDepth
    /// (parserOfStack 1)` tail: the just-parsed ident names the category.
    fn dynamic_quot_body(&mut self) -> PResult {
        let (t, at, sp) = self.peek_for_match();
        if t.kind != TokenKind::Ident {
            self.restore(&sp);
            return Err(self.fail_expecting("<quotation category>", at));
        }
        let cat_name = self.src[at..at + t.len as usize].to_string();
        self.bump(t, KIND_IDENT);
        self.expect_atom("|", false)?;
        self.quot_depth += 1;
        let r = self.category(&cat_name, 0);
        self.quot_depth -= 1;
        r
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

    /// `Prim::Many1Unbox` — ORACLE `many1Unbox p := withResultOf
    /// (many1NoAntiquot p) fun stx => if stx.getNumArgs == 1 then
    /// stx.getArg 0 else stx` (see the `Prim` variant's own doc
    /// comment). Deliberately NOT built on `many_impl`: that helper
    /// opens its `KIND_NULL` node UNCONDITIONALLY before the loop runs
    /// (it has to — the node must balance even on a mid-loop consuming
    /// failure), which is exactly the wrapper `many1Unbox` must NOT emit
    /// when exactly one item matches. Here the `Start` is deferred: run
    /// the same `many1`-shaped loop with no enclosing node at all, then
    /// retroactively splice a `Start(KIND_NULL)`/`Finish` pair around
    /// the collected events ONLY if 2+ items matched (`n == 1` leaves
    /// the single item's own events spliced in directly, unwrapped).
    fn many1_unbox_impl(&mut self, q: &Prim) -> PResult {
        let events_start = self.events.len();
        let mut n = 0usize;
        let result: PResult = loop {
            let sp = self.save();
            match self.run(q) {
                Ok(()) => {
                    if !self.consumed_since(&sp) {
                        // Same zero-width guard as `many_impl` (min = 1
                        // here always, so the first item is exempt).
                        if n == 0 {
                            n = 1;
                            continue;
                        }
                        let at = self.pos;
                        break Err(self.fail_expecting("<many1Unbox: zero-width item>", at));
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
        // Unlike `many_impl`, there is no dangling `Start` to balance on
        // a consuming failure — none was ever emitted — so a hard error
        // propagates directly, no wrapping node to close first.
        result?;
        if n == 0 {
            let at = self.pos;
            return Err(self.fail_expecting("<many1Unbox item>", at));
        }
        if n >= 2 {
            self.events
                .insert(events_start, PEvent::Ev(Event::Start(KIND_NULL)));
            self.finish();
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

    /// Sequence of `p` optionally separated by `sep`, indentation-scoped
    /// (Lean tactic/do-block sequencing: `by skip; skip` or one `skip`
    /// per line, but not `by skip skip` on one line; `structInstFields`'s
    /// `,`-separated field list is the same shape). ORACLE-PORT
    /// `Extra.lean` `sepByIndent`/`sepBy1Indent`: `withPosition $
    /// sepBy(1) (checkColGe >> p) sep (psep <|> checkColEq >>
    /// checkLinebreakBefore >> pushNone) (allowTrailingSep := true)`.
    /// Each item must be at or past the marker's column; between items,
    /// EITHER an explicit `sep` is consumed, OR — with no token at all —
    /// the next item starts on a new line at EXACTLY the marker's column
    /// (no separator needed when items are already visually separated by
    /// indentation; required when two share a line). `min` is 0
    /// (`sepByIndent`) or 1 (`sepBy1Indent`) — see `Prim::SepByIndent`'s
    /// doc comment.
    ///
    /// Task 9 fixes two divergences a fresh oracle probe found once a
    /// real caller (this task's `tacticSeq1Indented`/`tacticSeqBracketed`
    /// port) finally exercised this Task-6-authored, never-registered
    /// fn:
    /// 1. **Zero-item handling.** The oracle's `checkColGe >> p` failing
    ///    on the very FIRST attempt (whether from `checkColGe` itself or
    ///    from `p`) is just an ordinary non-consuming item failure to
    ///    `sepBy`/`sepBy1` — `sepBy` (min 0) accepts it as "zero items";
    ///    `sepBy1` (min 1) does not. The prior version special-cased a
    ///    `checkColGe` failure as an unconditional clean stop (right for
    ///    `sepBy`, wrong for `sepBy1` — e.g. `tacticSeq1Indented` must
    ///    hard-fail, not silently succeed empty, when `by` is followed by
    ///    nothing at all indented; the wrapping `tacticSeqIndentGt`
    ///    supplies its OWN explicit empty-fallback via a `checkColGt`
    ///    guard + `pushNone`, per `Term/Basic.lean:86-92` — this fn must
    ///    not pre-empt that).
    /// 2. **Implicit separator's tree contribution.** `psep <|>
    ///    (checkColEq .. checkLinebreakBefore .. pushNone)` (`..` standing
    ///    in for the oracle's `>>` here, so no wrapped doc line starts
    ///    with it — rustdoc/clippy treat a leading `>` as a markdown
    ///    blockquote marker) — the ACCEPTED implicit (same-column-
    ///    newline) branch still runs `pushNone` (`Basic.lean`:
    ///    pushes a real, empty `mkNullNode`) as its OWN sibling
    ///    contribution, exactly where an explicit separator atom would
    ///    sit. Confirmed against a fresh dump of a multi-line struct
    ///    instance (`{ a := x\n  b := y }`, no commas): `structInstFields`'
    ///    children interleave `structInstField, null{}, structInstField`
    ///    — that middle empty `null{}` IS the implicit separator's node,
    ///    not nothing. The prior version emitted no node at all here
    ///    (regression test below, previously asserting the WRONG
    ///    no-separator-node shape, is corrected as part of this fix).
    fn sep_by_indent(&mut self, item: &Prim, sep: &str, min: usize) -> PResult {
        // Marker-establishing lookahead — same role as `WithPosition`'s
        // own marker peek (Task 8 wave 2 review fix, see its doc
        // comment): finding WHERE the marker sits doesn't need to
        // consume anything, so this must be the READ-ONLY preview, not
        // the committing `peek_significant` — otherwise a leaked
        // trivia-skip here would be indistinguishable from real
        // `consumed_since` progress to an enclosing `many`/`many1` if
        // this call's own body later fails without independently
        // consuming further.
        let (_, at) = self.peek_significant_readonly();
        let lc = self.line_col(at);
        self.pos_stack.push(lc);
        self.start(KIND_NULL);
        let mut after_sep = false;
        let mut n = 0usize;
        let result: PResult = 'outer: loop {
            let sp = self.save();
            // `checkColGe >> p`, folded: a `checkColGe` failure is, from
            // `sepBy`'s perspective, indistinguishable from `p` itself
            // failing without consuming (`checkColGe` is zero-width) —
            // both funnel into the SAME mandatory-first-vs-clean-stop
            // decision below.
            let item_result: PResult = match self.check_col(|cur, saved| cur.1 >= saved.1) {
                Ok(()) => self.run(item),
                Err(f) => Err(f),
            };
            match item_result {
                Ok(()) => n += 1,
                Err(f) if self.consumed_since(&sp) => break 'outer Err(f),
                Err(f) => {
                    self.restore(&sp);
                    // allowTrailingSep := true — a trailing separator
                    // (explicit or implicit) with nothing following is a
                    // clean end. Otherwise, whether zero items is
                    // acceptable depends on `min` (see doc comment).
                    if after_sep || n >= min {
                        break 'outer Ok(());
                    }
                    break 'outer Err(f);
                }
            }
            let before_sep = self.pos;
            let sep_sp = self.save();
            match self.expect_atom(sep, false) {
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
                // Pure implicit-separator lookahead — only decides
                // whether to loop again, never itself consumes. Must be
                // the READ-ONLY preview (Task 8 wave 2 review fix
                // pattern, see `peek_significant_readonly`'s doc
                // comment): the committing `peek_significant` would
                // leak this trivia-skip as phantom consumption if the
                // `contains('\n')` check below then fails and control
                // falls through to `break 'outer Ok(())` with nothing
                // further consumed. Losslessness is preserved either
                // way: on the `continue 'outer` path the next
                // iteration's `self.run(item)` re-peeks (committing)
                // the SAME trivia span while dispatching the next
                // item's leading token, emitting it exactly once; on
                // the `break` path nothing between `before_sep` and
                // `next_at` has been committed yet, so whatever runs
                // after `sep_by_indent` returns is responsible for it,
                // same as any other non-consuming stop.
                let (_, next_at) = self.peek_significant_readonly();
                if self.src[before_sep..next_at].contains('\n') {
                    // Never-hang guard (review finding): unlike
                    // `sep_by_impl`'s `sep`, this branch's `pushNone` is
                    // zero-width BY CONSTRUCTION — it never advances
                    // `self.pos`. If `item` itself also managed to
                    // succeed without consuming anything this iteration
                    // (`!self.consumed_since(&sp)`, `sp` captured at the
                    // very top of this loop turn, before `item` ran),
                    // then taking this `continue 'outer` re-enters the
                    // loop at the exact same position with the exact
                    // same lookahead state — `item` is deterministic, so
                    // it would succeed zero-width again, forever. No
                    // currently-registered item is zero-width-successful,
                    // so this is unreached today, but the combinator is
                    // now a public shared primitive (`grammar.rs`) and
                    // must not rely on that. Refuse the loop instead:
                    // treat it as a clean stop, same as the `else`
                    // fallthrough below, and — critically — do NOT start
                    // the `null` node in that case, so the event stream
                    // stays balanced (an unmatched `start` with no
                    // `finish` would corrupt it).
                    if self.consumed_since(&sp) {
                        after_sep = true;
                        // `pushNone` — see doc comment fix (2) above: the
                        // implicit separator is a real, empty `null`
                        // node, not nothing.
                        self.start(KIND_NULL);
                        self.finish();
                        continue 'outer;
                    }
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
    /// none`), the check is unconstrained — always succeeds; these are
    /// all true `epsilonInfo` (zero-width) parsers in the oracle, never
    /// themselves tokenizing.
    ///
    /// Task 8 wave 2 review fix: uses the READ-ONLY preview
    /// (`peek_significant_readonly`), not the committing
    /// `peek_significant` a prior version of this fn used. The prior
    /// version's own doc comment reasoned that only the FAILURE path
    /// needed a restore (`checkColGtFn` reads `s.pos` directly with no
    /// tokenizing of its own) — true, but incomplete: the SUCCESS path
    /// left `self.pos` advanced past whatever trivia this fn's own peek
    /// happened to skip, and if whatever ran immediately afterward then
    /// failed WITHOUT independently consuming further, an enclosing
    /// `many`/`many1`'s `consumed_since` check couldn't tell that
    /// leaked trivia-skip apart from real progress — turning a clean,
    /// non-consuming stop into a hard, unrecoverable error. Read-only
    /// preview removes the hazard at the root (nothing to restore,
    /// since nothing was ever mutated): see
    /// `peek_significant_readonly`'s doc comment for the full mechanism
    /// and how this port's lazy-trivia architecture differs from the
    /// oracle's eager-trailing-trivia-attachment one. Found via
    /// `Term.pipeProj`'s `many argument` (`term_app.rs`); regression
    /// test in this file's test module.
    fn check_col(&mut self, ok: impl Fn((u32, u32), (u32, u32)) -> bool) -> PResult {
        let (_, at) = self.peek_significant_readonly();
        let cur = self.line_col(at);
        let Some(&saved) = self.pos_stack.last() else {
            return Ok(());
        };
        if ok(cur, saved) {
            Ok(())
        } else {
            Err(self.fail_expecting("<indentation>", at))
        }
    }

    /// ORACLE-PORT `checkTailWs`/`checkTailNoWs` (Basic.lean): whether
    /// the previously-parsed token has non-empty trailing trivia
    /// before the next significant token. Our event stream has no
    /// "trailing trivia" field on tokens (all trivia is its own flat
    /// event) so this is reconstructed two ways, covering both call
    /// patterns:
    /// - nothing has peeked ahead of the previous token yet, so a
    ///   READ-ONLY preview (`peek_significant_readonly` — Task 8 wave 2
    ///   review fix, see its doc comment) finds the next significant
    ///   token strictly past `self.pos` (`at > before`), WITHOUT
    ///   committing to that trivia-skip itself — whatever runs next
    ///   (this call's own caller, on success) does the real, committing
    ///   peek when it actually needs the position;
    /// - a peek already performed by an earlier combinator (e.g. the
    ///   `bump` that consumed the previous token, or an earlier REAL
    ///   `peek_significant`) already did that scan, so `self.pos == at`
    ///   on entry — the trailing event is then the tell.
    fn had_ws_before_current(&self) -> bool {
        let before = self.pos;
        let (_, at) = self.peek_significant_readonly();
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
        // A completed `category()` call collapses to ONE `PEvent::Sub`
        // (wave 2, Important 1), so the token this scan is looking for may
        // be inside a subtree rather than in `self.events`; the subtree's
        // precomputed `last_tok_trivia` answers for it without descending.
        last_tok_trivia(&self.events, &self.subtrees).unwrap_or(false)
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
    ///
    /// **Memoized** (Task 11b — untrusted-input never-hang hardening).
    /// ORACLE-PORT `categoryParser`/`withCacheFn` (`Basic.lean:1736`,
    /// `Lean/Parser/Types.lean:550`): real Lean wraps EVERY
    /// `categoryParser catName prec` call — this exact function — in a
    /// cache keyed by `(catName, pos, prec, savedPos?, forbiddenTk?)`
    /// (see `CatCacheKey`'s doc comment for the full field-by-field
    /// citation). Without it, `builtin/term.rs`'s
    /// `register_paren_family` — `paren`/`tuple`/`typeAscription`, THREE
    /// leading candidates that all share the `"(" >> hygieneInfo`
    /// prefix and then each independently recurse into `cat("term", 0)`
    /// at the identical inner position — repeats that recursion at
    /// EVERY nesting level: `(((((1)))))` at depth D does Θ(3^D) work
    /// (measured: depth 10 ~376ms, depth 15 >30s). Every sibling
    /// candidate at a given level is tried from the SAME outer
    /// savepoint (`longest_match`'s `self.restore(sp)` before each
    /// attempt), so it sees the identical `pos`/`rbp`/`forbidden`/
    /// `saved_pos` — the 2nd and 3rd sibling's `cat("term", 0)` become
    /// O(1) cache hits, collapsing the nesting to Θ(D) category calls.
    ///
    /// **Correctness** (a cache hit must reproduce EXACTLY what a
    /// re-parse would produce): a `category()` call has exactly three
    /// externally observable effects. (a) On success: the event/error
    /// slice appended between entry and exit, plus the final `pos`/
    /// `lhs_prec`. (b) On failure: nothing — the only failure path
    /// (the leading-dispatch `None` arm below) always `restore`s back
    /// to `entry_sp` first, so no event/error survives a failed call
    /// (`Savepoint::restore` doesn't touch `furthest_pos`/
    /// `furthest_expected` — see its own doc comment — which is
    /// exactly the field those globals are excluded from `Savepoint`
    /// for). (c) In BOTH cases, an update to the furthest-failure
    /// tally. (a)/(b) are stored verbatim as `CatOutcome` and replayed
    /// by *extending* `self.events`/`self.errors` with that exact
    /// slice: `Event::Token` carries an ABSOLUTE byte offset into the
    /// shared source (`tree.rs`), not an offset relative to the splice
    /// point, so appending a stored slice at a later point in the
    /// event stream reproduces bit-for-bit what a fresh run would have
    /// appended — no re-indexing, no risk of double-emitting or
    /// dropping trivia (the losslessness/event-balance invariant is
    /// preserved because the slice IS a contiguous, previously-real
    /// run of balanced `Start`/`Finish`/`Token`/`Missing` events, not a
    /// re-derived approximation). (c) is why `furthest_stack`/
    /// `apply_furthest_summary` exist: the tempting shortcut — snapshot
    /// the GLOBAL `furthest_pos`/`furthest_expected` at exit, replay
    /// that on a hit — is unsound, because those globals are a running
    /// max over the WHOLE parse and their value at one call's exit
    /// depends on the ambient tally on entry, which differs between
    /// the first (real) run and any later hit at the same key.
    /// `furthest_stack` instead tracks, per open call, a tally that
    /// starts from NOTHING (not from the ambient global) — a pure
    /// function of what happened during this call's own execution
    /// (including any nested cache hits, which fold their own stored
    /// tally back in via `apply_furthest_summary` — see that fn's doc
    /// comment), safe to store and replay against whatever the ambient
    /// tally happens to be at replay time.
    ///
    /// **`cat_depth` and the cache** (Task 11b review, Critical 1).
    /// `cat_depth` is ambient state — a Rust-stack-safety budget, not a
    /// grammar input — and a result can genuinely depend on it: if
    /// `MAX_CATEGORY_DEPTH` fires anywhere inside a call, that call
    /// returns a DEGRADED result (a failure, a truncated event slice, or
    /// a `"<max recursion depth exceeded>"` in its furthest-failure
    /// summary). Not caching the *direct* cap failure does not make the
    /// cache depth-blind-safe, because the capped call's ANCESTORS still
    /// return and still get cached. Under a key that doesn't record the
    /// depth they were computed at, such an entry can be replayed at a
    /// SHALLOWER `cat_depth` — where a fresh parse had budget to spare
    /// and would have succeeded — spuriously rejecting parseable input
    /// (`a_depth_capped_subparse_never_poisons_a_shallower_reach_of_the_
    /// same_key`, this file's test module, is exactly that shape: the
    /// same key reached at two depths one level apart, the deeper reach
    /// capped, the shallower one poisoned by it).
    ///
    /// So the key carries `depth_headroom`, and the invariant is:
    /// **an entry is only ever replayed in a state where re-running the
    /// body would compute it again.**
    ///
    /// - The call ran WITHOUT the cap firing inside it (`cap_hits`, the
    ///   monotone counter the cap arm bumps, did not move while the call
    ///   was open): its result is independent of the depth budget, so it
    ///   is stored under `depth_headroom: None` and may be replayed at
    ///   ANY `cat_depth`.
    /// - The cap DID fire inside: the result is a function of the budget
    ///   it had, so it is stored under `depth_headroom: Some(h)`, `h` =
    ///   the headroom this call started with, and is only ever replayed
    ///   at that same headroom — where it is, by determinism, exactly
    ///   what a re-parse computes.
    ///
    /// "The cap fired inside" means *in this call's dynamic extent*, and
    /// that includes INHERITING a capped result through a cache hit — a
    /// `Some(_)`-keyed hit bumps `cap_hits` too (see the hit path below,
    /// Task 11b review wave 2). Only counting fresh cap fires would leave
    /// a call that merely replayed a capped sub-result looking
    /// depth-independent, and store it under `None` — reopening exactly
    /// the failure mode above one level up.
    ///
    /// Lookup therefore tries the depth-independent key first and the
    /// current-headroom key second. Note what this buys over simply
    /// refusing to cache depth-tainted entries (the other candidate fix):
    /// past the cap, EVERY ancestor of the capped call is tainted, so
    /// "don't cache tainted" would leave the whole 3-way
    /// `paren`/`tuple`/`typeAscription` fanout un-memoized above the cap
    /// and hand back the Θ(3^depth) DoS this task exists to kill (
    /// measured: `parens_past_the_depth_cap_degrade_cleanly_not_hang` at
    /// depth 256 does not finish in 30s that way). Keying on the headroom
    /// keeps them memoized — sibling candidates at one nesting level all
    /// sit at the same `cat_depth`, hence the same headroom, hence the
    /// same key.
    ///
    /// To be precise about WHY that works, since it is easy to misread
    /// (Task 11b review wave 2, Important 2): `headroom =
    /// MAX_CATEGORY_DEPTH - cat_depth` is a *bijection* with `cat_depth`,
    /// so keying on it partitions the cache **identically** to keying on
    /// the absolute depth — it buys no extra sharing on its own, and
    /// nothing here would change if the field held `cat_depth` instead.
    /// The mechanism that actually collapses the fanout is the **`None`
    /// bucket**: the overwhelming majority of calls never touch the cap,
    /// go in depth-INDEPENDENT, and are therefore shared across every
    /// `cat_depth` at which their key is reached. `Some(h)` is only the
    /// quarantine for the rare depth-tainted entry, and there the
    /// same-depth-only sharing is exactly what keeps the *above-the-cap*
    /// fanout (where every entry is tainted) from re-exponentiating —
    /// siblings at one nesting level share a `cat_depth`, so they still
    /// hit each other. The cache stays bounded: at most (positions ×
    /// distinct headrooms) entries, i.e. O(n · cap), so the never-hang
    /// guarantee is polynomial-bounded, not exponential.
    ///
    /// One asymmetry is deliberate: a `None` (depth-independent) entry is
    /// replayed even at a DEEPER `cat_depth` than it was computed at,
    /// where a fresh parse might have capped. That can only ACCEPT more
    /// input, never reject valid input, and it cannot threaten the stack
    /// bound — a hit costs zero native stack, and native recursion only
    /// ever happens on a miss, which is gated by the cap.
    fn category(&mut self, name: &str, rbp: u32) -> PResult {
        let Some(cat) = self.snap_category(name) else {
            let at = self.pos;
            return Err(self.fail_expecting(&format!("<category {name}>"), at));
        };

        // Depth budget left for this call, i.e. the ambient state the cap
        // exposes to a parse (see "`cat_depth` and the cache" above).
        let headroom = MAX_CATEGORY_DEPTH.saturating_sub(self.cat_depth);
        let mut key = CatCacheKey {
            pos: self.pos,
            name: name.to_string(),
            rbp,
            forbidden: self.forbidden().map(str::to_string),
            saved_pos: self.pos_stack.last().copied(),
            // Depth-INDEPENDENT entries first: valid at any `cat_depth`,
            // and the overwhelmingly common case (nothing in a normal
            // parse ever comes near the cap).
            depth_headroom: None,
            quot_depth: self.quot_depth,
        };
        let mut hit = self.cat_cache.get(&key).cloned();
        // Did the entry we matched come from the depth-DEPENDENT bucket?
        // (`key.depth_headroom` is `None` for the first probe, `Some(_)`
        // for the second, so this is just "did the second probe win".)
        let mut hit_is_depth_dependent = false;
        if hit.is_none() {
            // …then an entry the cap DID shape, which only this same
            // headroom may replay.
            key.depth_headroom = Some(headroom);
            hit = self.cat_cache.get(&key).cloned();
            hit_is_depth_dependent = hit.is_some();
        }
        if let Some(entry) = hit {
            if hit_is_depth_dependent {
                // Task 11b review wave 2 (Critical 1, reopened): a
                // `Some(_)`-keyed entry IS, by definition, a depth-cap
                // artifact — the cap fired inside the call that produced
                // it. INHERITING it makes this call's result just as much
                // an artifact of the ambient depth budget as computing it
                // afresh would have, so every currently-open ancestor must
                // be tainted exactly as a fresh cap fire would taint them
                // (`cap_hits` is the monotone counter each open call
                // diffs on exit — see the cap arm below and this fn's doc
                // comment). Without this bump an ancestor that merely
                // REPLAYS a capped sub-result gets stored under
                // `depth_headroom: None`, i.e. advertised as valid at any
                // `cat_depth`, and replaying THAT at a shallower depth —
                // where a fresh parse had budget and would have succeeded
                // — rejects valid input (regression test:
                // `a_cache_hit_on_a_depth_capped_entry_taints_its_
                // ancestors_too`). A `None` hit needs no bump: a
                // depth-independent result cannot make its parent
                // depth-dependent.
                self.cap_hits += 1;
            }
            self.apply_furthest_summary(&entry.furthest);
            return match entry.outcome {
                CatOutcome::Ok { sub, end, lhs_prec } => {
                    // O(1), whatever the subtree's size: one shared
                    // reference, not a copy of its events (wave 2,
                    // Important 1 — see `PEvent`). This is also what makes
                    // the ENCLOSING call's own eventual entry small: it
                    // captures this `Sub` marker, not the subtree behind it.
                    self.events.push(PEvent::Sub(sub));
                    self.errors.push(PError::Sub(sub));
                    self.pos = end;
                    self.lhs_prec = lhs_prec;
                    Ok(())
                }
                CatOutcome::Err => Err(Fail),
            };
        }

        if self.cat_depth >= MAX_CATEGORY_DEPTH {
            // Untrusted-input totality: `Category` is the ONE place
            // input (nested parens, deeply chained trailing forms,
            // …) can drive recursion depth — see `MAX_CATEGORY_DEPTH`.
            // Deliberately checked AFTER the cache lookup (a hit costs
            // no native stack). Bumping `cap_hits` marks every
            // currently-open call as depth-dependent: this failure is an
            // artifact of the ambient depth budget, so neither it nor
            // any ancestor result computed from it may be cached as
            // depth-INDEPENDENT (see this fn's doc comment, "`cat_depth`
            // and the cache"). The direct failure itself is not cached
            // at all — it is already O(1).
            self.cap_hits += 1;
            let at = self.pos;
            return Err(self.fail_expecting("<max recursion depth exceeded>", at));
        }
        let cap_hits_on_entry = self.cap_hits;
        self.cat_depth += 1;
        self.furthest_stack.push(None);
        let saved_prec = self.prec;
        self.prec = rbp;
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
        // Task 11b: also doubles as the cache-slice base index — this
        // MUST be the very first savepoint taken in the call (nothing
        // between `self.prec = rbp` above and here touches
        // `pos`/`events`/`errors`), since `key.pos` was read before
        // either.
        let entry_sp = self.save();
        let r = (|| {
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
            let mut parsers: Vec<Prim> = idxs
                .iter()
                .map(|&i| cat.leading_parsers[i].clone())
                .collect();
            // M3b1 Task 6: same-file overlay additions are ADDITIONS —
            // never displace a base production — so they're appended
            // AFTER the base candidates (registration order), run
            // through the identical `first_tok_matches` rule
            // (`dispatch_overlay`) and then the SAME `longest_match`
            // below: one dispatch/selection path, base and overlay
            // candidates just feed the same list. Empty overlay ⇒
            // `category_delta` is `None` ⇒ `parsers` is unchanged from
            // above, byte-identical to M3a.
            if let Some(cd) = self.overlay.category_delta(name) {
                let suppress = suppress_plain_ident_for(cat, text, t.kind, true);
                parsers.extend(dispatch_overlay(cd, text, t.kind, true, suppress));
            }
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
                // Task 8 wave 2 review fix: this dispatch lookahead uses
                // the READ-ONLY preview (`peek_significant_readonly`),
                // not the committing `peek_significant` — it's purely a
                // "what token comes next, does anything qualify"
                // decision, not itself a real parse. See
                // `peek_significant_readonly`'s doc comment for the full
                // mechanism/oracle citation; regression test
                // `trailing_many_finding_nothing_after_a_real_item_does_
                // not_leak_as_phantom_consumption` (this file's test
                // module) — reproducing the shape `Term.pipeProj`'s
                // `many argument` (`builtin/term/term_app.rs`) exposed.
                //
                // Intended side effect on node placement (NOT a
                // regression): before this fix, this same lookahead
                // committed the whitespace between a function and its
                // first argument BEFORE `sp` below was captured, so that
                // trivia ended up as a preceding sibling of the winning
                // body's own generated events — still inside the
                // eventual `Term.app` wrap (inserted retroactively at
                // `lhs_events`, above), but OUTSIDE `many1(argument())`'s
                // own null-node wrap (`many_impl`'s `self.start(KIND_NULL)`,
                // which hadn't run yet). Now that this peek is read-only,
                // `sp` is captured BEFORE the whitespace, so the winning
                // body (`Term.app`'s `many1(argument())`) opens its null
                // node first and the whitespace is only actually
                // committed later — when the first argument's own
                // leading dispatch peeks forward — landing it INSIDE
                // that null node as its first child instead. Round-trip
                // and canon (trivia-free) output are both blind to this
                // shift; it is unrelated to (and does not conflict with)
                // `leading_trivia_stays_outside_a_trailing_wrap_...`
                // (this file's test module), which is about the LHS's
                // OWN leading trivia staying outside a later trailing
                // wrap, not about a trailing production's internal
                // argument trivia.
                let (t, at) = self.peek_significant_readonly();
                if t.kind == TokenKind::Eof {
                    break;
                }
                let text = &self.src[at..at + t.len as usize];
                let idxs = dispatch(cat, text, t.kind, false);
                let mut candidates: Vec<Prim> = idxs
                    .iter()
                    .map(|&idx| cat.trailing_parsers[idx].clone())
                    .collect();
                // M3b1 Task 6: overlay trailing additions, same
                // append-after-base rule as the leading side above (and
                // the same no-op-when-empty guarantee).
                if let Some(cd) = self.overlay.category_delta(name) {
                    let suppress = suppress_plain_ident_for(cat, text, t.kind, false);
                    candidates.extend(dispatch_overlay(cd, text, t.kind, false, suppress));
                }
                let qualifying: Vec<Prim> = candidates
                    .into_iter()
                    .filter(|p| match p {
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
                    .map(|p| match p {
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
                        let Prim::TrailingNode { kind, prec, .. } = &qualifying[w.idx] else {
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
                        // (The lhs may by now be a single `PEvent::Sub`
                        // marker standing for a whole memoized subtree —
                        // wave 2, Important 1. That changes nothing here:
                        // `lhs_events` is still the index of the lhs's first
                        // top-level event, and wrapping is still one `Start`
                        // inserted in front of it.)
                        self.events
                            .insert(lhs_events, PEvent::Ev(Event::Start(*kind)));
                        self.events.push(PEvent::Ev(Event::Finish));
                        self.lhs_prec = *prec;
                    }
                    None => break,
                }
            }
            Ok(())
        })();
        self.prec = saved_prec;
        self.cat_depth -= 1;
        let local_furthest = self
            .furthest_stack
            .pop()
            .expect("pushed exactly once above, popped exactly once here");
        // Task 11b review (Critical 1): if `cap_hits` moved while this
        // call was open, the depth cap fired inside its dynamic extent,
        // so `r` (and/or the event slice, and/or the furthest summary)
        // reflects the depth budget it happened to have — not just the
        // key. Record that budget in the key, so this entry can only ever
        // be replayed at the same headroom (where re-running the body
        // recomputes it exactly); otherwise the entry is depth-blind and
        // replayable anywhere. See this fn's doc comment.
        key.depth_headroom = (self.cap_hits != cap_hits_on_entry).then_some(headroom);
        // Task 11b: cache both outcomes (see this fn's doc comment for
        // why a failure is just as safe to memoize as a success: it has
        // no events/errors of its own, only the furthest-failure
        // summary).
        let outcome = match &r {
            Ok(()) => {
                // Move this call's own output OUT of the live streams and
                // into the subtree arena, leaving a single `Sub` marker
                // behind (wave 2, Important 1 — see `PEvent`). Nested
                // category calls already collapsed to `Sub` markers the same
                // way before returning here, so what we move is only THIS
                // call's own events/errors: each event is retained exactly
                // once across the whole parse, not once per enclosing call.
                //
                // Observationally this is a no-op for every other part of
                // the parser: `flatten_events` expands the markers back into
                // the identical event stream at tree-build time, and
                // `self.events.len()` (`save`/`lhs_events`) only ever indexes
                // TOP-LEVEL boundaries, never into a subtree.
                let sub = self.subtrees.len();
                let events = self.events.split_off(entry_sp.events);
                let errors = self.errors.split_off(entry_sp.errors);
                let last_tok_trivia = last_tok_trivia(&events, &self.subtrees);
                self.subtrees.push(Subtree {
                    events,
                    errors,
                    last_tok_trivia,
                });
                self.events.push(PEvent::Sub(sub));
                self.errors.push(PError::Sub(sub));
                CatOutcome::Ok {
                    sub,
                    end: self.pos,
                    lhs_prec: self.lhs_prec,
                }
            }
            Err(Fail) => CatOutcome::Err,
        };
        self.cat_cache.insert(
            key,
            CatCacheEntry {
                outcome,
                furthest: local_furthest,
            },
        );
        r
    }

    // ---- output -------------------------------------------------------
    /// The diagnostics recorded so far, in push order. Materializes the
    /// `PError` stream (expanding memoized subtrees — see `PEvent`); the
    /// live `self.errors` is not a flat list any more.
    ///
    /// Cost: O(total events) — it walks and materializes the *entire*
    /// event stream on every call, so it must never be called from inside
    /// the per-command loop (that would make `parse_module` quadratic);
    /// call it once, at the end of a parse.
    pub(crate) fn errors(&self) -> Vec<ParseError> {
        flatten_errors(&self.errors, &self.subtrees)
    }

    /// Fold the event stream into a lossless tree, using `merged_kinds`
    /// (M3b1 Task 6: base kinds + this `Ps`'s overlay's own kinds — a
    /// plain `Arc::clone` of the snapshot's interner when the overlay has
    /// none, same as M3a's `self.kinds.clone()` here before this task).
    pub(crate) fn finish_into_tree(self) -> (SyntaxTree, Vec<ParseError>) {
        let kinds = self.merged_kinds();
        let events = flatten_events(&self.events, &self.subtrees);
        let errors = flatten_errors(&self.errors, &self.subtrees);
        let tree = build_tree(self.src, &events, kinds);
        (tree, errors)
    }
}

/// `LeadingIdentBehavior::Symbol`'s ident-suppression flag — factored
/// out of `dispatch` (M3b1 Task 6) so `category()` can compute it
/// exactly ONCE per read point and apply the SAME value to both the
/// base dispatch (`dispatch`) and the overlay dispatch
/// (`dispatch_overlay`), rather than two call sites each re-deriving it
/// (possibly inconsistently). Behavior is unchanged from before the
/// refactor — see `dispatch`'s own doc comment for the full ORACLE-PORT
/// `indexed`/`LeadingIdentBehavior` citation this implements.
///
/// `leading &&`: ORACLE-PORT `trailingLoop` (Basic.lean:1932) hard-codes
/// `LeadingIdentBehavior.default` for its OWN ident dispatch — only
/// `leadingParserAux` (:1910) is passed the category's actual
/// `behavior`. A category's `ident_behavior` therefore must never
/// suppress anything on the TRAILING side, regardless of its own value
/// (`Symbol`/`Both`/`Default` alike) — trailing dispatch always behaves
/// as `Default` (M3a Task 11 item (b)). Inert today (no trailing row in
/// `attr`/`prio`/`tactic` — the only non-`Default` categories — actually
/// collides with a same-text `Ident`-keyed trailing entry), but a real
/// divergence from the oracle otherwise.
fn suppress_plain_ident_for(cat: &Category, text: &str, kind: TokenKind, leading: bool) -> bool {
    let table = if leading { &cat.leading } else { &cat.trailing };
    leading
        && kind == TokenKind::Ident
        && cat.ident_behavior == LeadingIdentBehavior::Symbol
        && table
            .iter()
            .any(|(f, _)| matches!(f, FirstTok::Sym(s) if s == text))
}

/// Whether first-token index entry `f` matches the upcoming `(text,
/// kind)` token — the ONE selection rule every candidate list in this
/// file is dispatched through: the base `Category::leading`/`trailing`
/// tables (via `dispatch`) AND, since M3b1 Task 6, an `Overlay`'s
/// `CategoryDelta::leading`/`trailing` (via `dispatch_overlay`). Pulled
/// out so overlay candidates are filtered by the IDENTICAL logic rather
/// than a second, driftable copy of it (Task 6 brief: "Do not duplicate
/// the dispatch logic").
fn first_tok_matches(
    f: &FirstTok,
    text: &str,
    kind: TokenKind,
    suppress_plain_ident: bool,
) -> bool {
    match f {
        FirstTok::Any => true,
        // A token-table symbol lexes as `Atom` (even when ident-shaped,
        // e.g. `do`/`then` — ORACLE-PORT `next_token`'s munch-competition
        // rule in lex.rs), so the `Atom` arm covers every real
        // `Prim::Symbol`. The `Ident`-with-matching-text arm is what
        // makes `Prim::NonReservedSymbol` (`level`'s `max`/`imax`)
        // dispatchable at all: ORACLE-PORT `nonReservedSymbolInfo`
        // (Basic.lean) — `nonReservedSymbol sym (includeIdent := true)`
        // sets `firstTokens := .tokens [sym, "ident"]`, a DUAL
        // registration, precisely because `sym`'s text is deliberately
        // never harvested into the token table (grammar.rs's
        // `walk_symbols` doc comment) and so can only ever lex as a
        // plain `Ident`, never an `Atom`. A real `Symbol`'s text, by
        // contrast, always lexes as `Atom` once harvested (never
        // `Ident`), so this second arm is a dead branch for it —
        // extending the match costs real `Symbol` dispatch nothing and
        // is exactly what makes a `NonReservedSymbol`-led production
        // reachable at all. `first_tok` maps both `Symbol` and
        // `NonReservedSymbol` to the same `FirstTok::Sym` (grammar.rs),
        // so this one arm covers both.
        FirstTok::Sym(s) => {
            (kind == TokenKind::Atom && s == text) || (kind == TokenKind::Ident && s == text)
        }
        FirstTok::Ident => kind == TokenKind::Ident && !suppress_plain_ident,
        FirstTok::Num => kind == TokenKind::Num,
        FirstTok::Scientific => kind == TokenKind::Scientific,
        FirstTok::Str => kind == TokenKind::Str,
        FirstTok::Char => kind == TokenKind::Char,
        FirstTok::NameLit => kind == TokenKind::NameLit,
    }
}

/// Collect the `leading`/`trailing` candidate indices (registration
/// order) whose `FirstTok` matches the upcoming token — `FirstTok::Any`
/// entries are unindexed and always tried, alongside whichever
/// specific-token entries matched (ORACLE-PORT `PrattParsingTables`:
/// the indexed table lookup plus the always-tried `leadingParsers`/
/// `trailingParsers` list, collapsed here into one paired vector — see
/// `Category`'s doc comment).
///
/// ORACLE-PORT `Basic.lean`'s `indexed` — the `LeadingIdentBehavior`
/// dispatch (M3a Task 10 review Finding 1). When the upcoming token
/// lexes as `Ident`, `indexed` first asks whether ANY parser is
/// registered under the literal key equal to the ident's own text (a
/// `nonReservedSymbol`-keyed row, e.g. `Attr.extern`'s `"extern"` —
/// `first_tok` maps both `Prim::Symbol` and `Prim::NonReservedSymbol`
/// to the same `FirstTok::Sym`, so that's the `FirstTok::Sym(s) if s ==
/// text` case below); what happens next depends on the category's
/// `LeadingIdentBehavior`:
///   - `Symbol` — if such a literal-key match exists, run ONLY those
///     candidates; the generic `Ident`-keyed candidates (e.g.
///     `Attr.simple`'s bare `ident`) are not even tried. This is the
///     substantive fix: previously every `FirstTok::Ident` entry was
///     included unconditionally alongside any `FirstTok::Sym` text
///     match, so e.g. `Attr.simple` could out-consume (or, on a strict
///     tie, lose a registration-order race against) `Attr.extern` for
///     input like `@[extern foo]` — a divergence from the oracle, which
///     never even considers `Attr.simple` there (`attr`'s category
///     behavior is `.symbol`, `Attr.lean:20`), so it always rejects.
///   - `Default`/`Both` — union the literal-key match (if any) with the
///     generic `Ident`-keyed candidates, exactly as before (this is
///     also what makes `Prim::NonReservedSymbol` with an implied
///     `includeIdent := true`, e.g. `level`'s `max`/`imax`
///     `Level.lean:27,29`, reachable at all: its ONLY registration is
///     the literal-key `FirstTok::Sym`, unioned in here since `level`'s
///     behavior is `.default`).
///
/// Under `Symbol` behavior, a literal-key ident match suppresses the
/// generic `Ident`-keyed candidates entirely — precomputed once
/// (`suppress_plain_ident_for`) so the single ordered dispatch pass
/// (which must preserve registration order for `longest_match`'s
/// tie-break) can just filter (`first_tok_matches`).
fn dispatch(cat: &Category, text: &str, kind: TokenKind, leading: bool) -> Vec<usize> {
    let table = if leading { &cat.leading } else { &cat.trailing };
    let suppress_plain_ident = suppress_plain_ident_for(cat, text, kind, leading);
    table
        .iter()
        .filter_map(|(f, idx)| {
            first_tok_matches(f, text, kind, suppress_plain_ident).then_some(*idx)
        })
        .collect()
}

/// Overlay twin of `dispatch` (M3b1 Task 6): same `first_tok_matches`
/// rule, applied to an `Overlay`'s `CategoryDelta` instead of the base
/// `Category`. A `CategoryDelta` stores `(FirstTok, Prim)` pairs
/// directly rather than `(FirstTok, usize)` indices into a separate
/// parser vec (Task 1/5's doc comment on `CategoryDelta`: an overlay's
/// additions are small, same-file, not a whole snapshot's worth of
/// productions), so this returns cloned `Prim`s rather than indices.
/// `suppress_plain_ident` is the caller's (`category`'s) own value,
/// computed once from the BASE category via `suppress_plain_ident_for`
/// — `LeadingIdentBehavior` is a base-`Category`-level concept with no
/// per-overlay override (M3b1 only ever EXTENDS an existing category,
/// never adds a new one), so the base category's own flag governs both
/// halves of the merged candidate list.
fn dispatch_overlay(
    cd: &CategoryDelta,
    text: &str,
    kind: TokenKind,
    leading: bool,
    suppress_plain_ident: bool,
) -> Vec<Prim> {
    let table = if leading { &cd.leading } else { &cd.trailing };
    table
        .iter()
        .filter(|(f, _)| first_tok_matches(f, text, kind, suppress_plain_ident))
        .map(|(_, p)| p.clone())
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

    /// Run a deep/adversarial parse on a thread with `MIN_STACK_BYTES`,
    /// AND bound it in wall-clock time (`libtest` has no per-test timeout,
    /// so an `elapsed < BUDGET` assertion placed AFTER the call cannot
    /// turn a hang into a failure — it never runs). Task 11b review,
    /// Critical 2 + Important 3.
    ///
    /// The `stack_size` here is load-bearing and, unlike
    /// `tests/never_hang.rs`'s `in_worker` (which dropped it in wave 2),
    /// must stay: these unit tests drive `Ps::run`/`Ps::category` and
    /// `parse_cat` DIRECTLY, below `parse_module` — so they bypass the
    /// worker `parse_module` sizes for itself and have to supply the
    /// contracted stack themselves. `libtest`'s own test threads get
    /// 2 MiB, an eighth of it.
    fn in_worker<T: Send + 'static>(label: &str, f: impl FnOnce() -> T + Send + 'static) -> T {
        const BUDGET: std::time::Duration = std::time::Duration::from_secs(30);
        let (tx, rx) = std::sync::mpsc::channel();
        let h = std::thread::Builder::new()
            .stack_size(MIN_STACK_BYTES)
            .spawn(move || {
                let _ = tx.send(f());
            })
            .expect("spawn worker");
        match rx.recv_timeout(BUDGET) {
            Ok(v) => {
                h.join().expect("worker thread panicked");
                v
            }
            // The closure panicked (assert failed / parser panicked):
            // the sender was dropped without ever sending.
            Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
                std::panic::resume_unwind(h.join().expect_err("disconnected without a panic"))
            }
            Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
                panic!("{label}: still running after {BUDGET:?} — the parser hung")
            }
        }
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
        b.category("term", LeadingIdentBehavior::Default);
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
        b.category("c", LeadingIdentBehavior::Default);
        b.leading2("c", "short", MAX_PREC, sym("x"));
        b.leading2("c", "long", MAX_PREC, seq([sym("x"), sym("!")]));
        let snap = b.finish();
        assert_eq!(parse_cat(&snap, "x !"), "(long 'x' '!')");
        assert_eq!(parse_cat(&snap, "x"), "(short 'x')");
    }

    #[test]
    fn with_position_col_gt() {
        let mut b = SnapshotBuilder::new();
        b.category("c", LeadingIdentBehavior::Default);
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
        b.category("term", LeadingIdentBehavior::Default);
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
        b.category("c", LeadingIdentBehavior::Default);
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
        let errors = ps.errors();
        assert_eq!(
            errors.len(),
            1,
            "the embedded unterminated-raw-string lex error must survive \
             the leading longest-match splice, not be discarded"
        );
        assert_eq!(errors[0].code, "E0302");
    }

    #[test]
    fn sep_by_indent_semicolon_same_column_no_semicolon_needed() {
        // ORACLE-PORT `Term/Basic.lean` `sepBy1IndentSemicolon` (min 1,
        // matching `tacticSeq1Indented`'s real use): items on their own
        // line at the marker's column don't need `;`; two on the SAME
        // line do. Task 9 fix: the implicit (same-column-newline)
        // separator is itself a real, empty `null` node (`pushNone`) —
        // NOT nothing, as a prior version of both the impl and this test
        // wrongly had it (see `sep_by_indent`'s doc comment fix (2)).
        let mut b = SnapshotBuilder::new();
        b.category("c", LeadingIdentBehavior::Default);
        b.leading2(
            "c",
            "seq",
            MAX_PREC,
            Prim::WithPosition(Arc::new(sep_by1_indent(Prim::Ident, ";"))),
        );
        let snap = b.finish();
        assert_eq!(
            parse_cat(&snap, "a\nb\nc"),
            "(seq (null a (null) b (null) c))"
        );
        assert_eq!(parse_cat(&snap, "a; b; c"), "(seq (null a ';' b ';' c))");
        assert_eq!(parse_cat(&snap, "a; b;"), "(seq (null a ';' b ';'))");

        // Review finding 2 (Task 8 wave 2): `sep_by_indent`'s own
        // marker-establishing peek and its pure implicit-separator
        // lookahead (the `if coleq { .. }` branch) must be the READ-ONLY
        // preview, not the committing `peek_significant` — the same
        // hazard class fixed elsewhere that wave (`check_col`/
        // `had_ws_before_current`/`WithPosition`'s marker peek/the
        // trailing loop's dispatch peek). Losslessness check with
        // `parse_cat_with_trivia`: the trivia BETWEEN two implicitly-
        // separated items (here, a comment plus surrounding whitespace)
        // must land in the tree EXACTLY ONCE — committed by the second
        // item's own leading token match, not by either of the
        // read-only lookaheads — never dropped, never duplicated.
        // The empty separator node is pushed (zero-width, no peek of its
        // own) BEFORE the trivia between it and `b` — `b`'s own leading
        // dispatch is what commits that trivia-skip, same lazy-trivia
        // architecture as every other zero-width marker in this port
        // (e.g. `EmitEmptyIdent`'s doc comment).
        assert_eq!(
            parse_cat_with_trivia(&snap, "a -- hi\nb"),
            "(seq (null a (null) <ws> <ws> b))"
        );
    }

    #[test]
    fn sep_by_indent_min_zero_accepts_empty_and_general_separator() {
        // Task 9 fix (1): `sepByIndent` (min 0 — `tacticSeqBracketed`'s
        // `{ }`, `Term.structInstFields`) must accept ZERO items when the
        // very first attempt fails without consuming — a prior version
        // of `sep_by_indent` unconditionally treated ANY `checkColGe`
        // failure as a clean stop regardless of `min`, which happened to
        // give the right answer here but for the wrong reason (see the
        // OTHER new test below for where that reasoning breaks for
        // `min: 1`). Also exercises the generalized `sep` parameter
        // (`,`, not `;` — `Term.structInstFields`'s real separator).
        let mut b = SnapshotBuilder::new();
        b.category("c", LeadingIdentBehavior::Default);
        b.leading2(
            "c",
            "seq",
            MAX_PREC,
            Prim::WithPosition(Arc::new(sep_by_indent(Prim::Ident, ","))),
        );
        let snap = b.finish();
        assert_eq!(parse_cat(&snap, ""), "(seq (null))");
        assert_eq!(parse_cat(&snap, "a, b, c"), "(seq (null a ',' b ',' c))");
        // Multi-line, no comma — the `structInstFields` divergence this
        // task closes (see `builtin/term.rs::struct_inst_fields`):
        // matches the oracle's `structInstField, null{}, structInstField`
        // shape (probed against a fresh dump of a multi-line struct
        // instance, task-9 report).
        assert_eq!(parse_cat(&snap, "a\nb"), "(seq (null a (null) b))");
    }

    #[test]
    fn sep_by_indent_zero_width_item_terminates() {
        // Review finding 1: `sep_by_indent`'s implicit-separator branch
        // (the `pushNone` continue) is zero-width by construction — it
        // never advances `self.pos`. If `item` itself ALSO succeeds
        // zero-width, the pre-fix loop re-derives the exact same
        // decision at the exact same position forever: no currently-
        // registered item is zero-width-successful, but the combinator
        // is now a public shared primitive (`grammar.rs`), so this must
        // hold for ANY item, not just today's callers.
        //
        // Toy item: `Prim::EmitEmptyIdent` — an existing, real primitive
        // (`hygieneInfoFn`'s port) that ALWAYS succeeds without moving
        // `self.pos` (see its doc comment). It is not used as a
        // `sep_by_indent` item by any real grammar row; it's used here
        // purely as a minimal zero-width-success witness.
        //
        // Run via `run_toy` (direct `Ps::run`), NOT `parse_cat`/a
        // registered category production: a category's own leading-
        // token dispatch does a COMMITTING peek to find the first
        // significant token before invoking the row's `Prim` at all,
        // which would already consume the leading newline this test
        // needs `sep_by_indent` itself to see as "unconsumed" — that
        // was tried first and it defeated the repro (the newline was
        // gone by the time `sep_by_indent` ran, so the implicit-
        // separator branch legitimately never fired). `run_toy` invokes
        // `self.run(p)` directly at `self.pos == 0`, so no such
        // pre-consumption happens.
        //
        // `src = "\nx"`: the marker is established by peeking past the
        // leading newline to "x" (read-only, so `self.pos` stays 0).
        // Every loop iteration then finds: `checkColGe` holds (current
        // column == marker column, since nothing has moved); `item`
        // succeeds zero-width; no explicit `,` follows (the failed
        // match attempt commits-then-restores, netting no change);
        // the implicit-separator lookahead sees the SAME leftover
        // leading newline (still unconsumed, since nothing has
        // advanced `self.pos` past it) and reports "linebreak since
        // last item" — true every time. Pre-fix, that satisfies the
        // implicit-separator branch unconditionally and loops forever
        // (confirmed empirically: temporarily reverting just the
        // `self.consumed_since(&sp)` guard added by this fix and
        // re-running this exact test never returned — no output, no
        // pass/fail, had to be killed by hand — see task-9-report.md's
        // "Fix wave 1" section for the transcript).
        //
        // Post-fix: the guard recognizes "nothing moved this
        // iteration" and refuses the `continue`, breaking cleanly
        // instead — one item parsed, no separator node emitted (an
        // unmatched `start` for that node would corrupt the event
        // stream), min (0) is satisfied.
        let mut kinds = KindInterner::new();
        let prim = Prim::WithPosition(Arc::new(sep_by_indent(Prim::EmitEmptyIdent, ",")));
        let (tree_sexpr, errors) = run_toy("\nx", &[","], &prim, &mut kinds);
        assert_eq!(tree_sexpr, "(root (null ))");
        assert_eq!(errors, 0);
    }

    #[test]
    fn sep_by1_indent_min_one_hard_fails_on_zero_items() {
        // Task 9 fix (1), the `min: 1` side: `sepBy1IndentSemicolon`
        // (`tacticSeq1Indented`'s real body) must FAIL — not silently
        // succeed empty — when no item is found at all (its wrapping
        // `tacticSeqIndentGt` supplies the oracle's OWN explicit
        // empty-tactic-sequence fallback via a separate `checkColGt`
        // guard + `pushNone`, `Term/Basic.lean:86-92`; this fn must not
        // pre-empt that by silently accepting zero items itself).
        let mut b = SnapshotBuilder::new();
        b.category("c", LeadingIdentBehavior::Default);
        b.leading2(
            "c",
            "seq",
            MAX_PREC,
            Prim::WithPosition(Arc::new(sep_by1_indent(Prim::Ident, ";"))),
        );
        let snap = b.finish();
        let mut ps = Ps::new("", &snap);
        let r = ps.run(&Prim::Category {
            name: "c".to_string(),
            rbp: 0,
        });
        assert!(r.is_err(), "sepBy1Indent must hard-fail on zero items");
    }

    #[test]
    fn with_forbidden_blocks_the_exact_token_only_within_its_scope() {
        // ORACLE-PORT `mkTokenAndFixPos`/`withForbidden` (Basic.lean):
        // Task 9's `doFor`/`doUnless`/etc. wrap their iterable/condition
        // in `withForbidden "do" termParser` so the term Pratt-loop can't
        // eat the construct's OWN trailing `"do "` keyword as an
        // application argument (`Term.do`'s prec, `argPrec`, is exactly
        // `ARG_PREC` — high enough to otherwise qualify). Regression for
        // an early version of this port that lacked `WithForbidden`
        // entirely (see task-9 report).
        let mut k = KindInterner::new();

        // (1) A bare forbidden match fails cleanly (no consumption).
        let p = with_forbidden("do", sym("do"));
        let (_, errs) = run_toy("do", &["do"], &wrap_root(&mut k, p), &mut k);
        assert_eq!(errs, 1, "forbidden token must fail to match");

        // (2) `withoutForbidden` nested inside re-enables it.
        let p = with_forbidden("do", without_forbidden(sym("do")));
        let (s, errs) = run_toy("do", &["do"], &wrap_root(&mut k, p), &mut k);
        assert_eq!(errs, 0);
        assert_eq!(s, "(root (r 'do'))");

        // (3) The scope is exactly as wide as its own body — once
        // `WithForbidden`'s `q` returns, a LATER match of the same token
        // outside the scope succeeds normally (mirrors `doFor`'s own
        // trailing `"do "` keyword, reached only after the iterable's
        // `withForbidden`-scoped term parse has already returned).
        let p = seq([with_forbidden("do", Prim::Ident), sym("do")]);
        let (s, errs) = run_toy("x do", &["do"], &wrap_root(&mut k, p), &mut k);
        assert_eq!(errs, 0);
        assert_eq!(s, "(root (r x 'do'))");
    }

    #[test]
    fn adversarial_nesting_terminates_without_overflow() {
        // Untrusted-input totality: `Category` recursion is the ONE
        // place input can drive parser recursion depth (nested parens
        // here). Well past `MAX_CATEGORY_DEPTH`, this must return an
        // error — gracefully, never panicking or overflowing the
        // stack (if it does, this test crashes the process rather
        // than failing an assert, which is exactly the property being
        // checked — hence `in_worker`, which runs it on the stack the
        // crate's contract actually promises).
        in_worker("adversarial nesting", || {
            let mut b = SnapshotBuilder::new();
            b.category("e", LeadingIdentBehavior::Default);
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

            // A depth well within the cap still parses correctly, with
            // the expected nesting.
            let depth = 10usize;
            let shallow = "(".repeat(depth) + "x" + &")".repeat(depth);
            let mut expected = "(atom x)".to_string();
            for _ in 0..depth {
                expected = format!("(paren '(' {expected} ')')");
            }
            assert_eq!(parse_cat(&snap, &shallow), expected);
        });
    }

    /// Task 11b review, CRITICAL 1: a `category()` result computed under
    /// a subtree that hit `MAX_CATEGORY_DEPTH` must never be cached —
    /// otherwise a later, SHALLOWER reach of the same cache key replays
    /// a depth-cap artifact and rejects input a fresh parse accepts.
    ///
    /// The shape below reaches the identical key `(pos of "(y)", "e", 0)`
    /// at two different `cat_depth`s, one level apart:
    ///
    /// - `unary` (`"-" e`) tried FIRST, twice: `- ‖ - ‖ (y)` — reaches it
    ///   at depth d+2, leaving only enough budget for the `paren` inside
    ///   to fire the cap. So the call at that key FAILS.
    /// - `double` (`"-" "-" e`) tried second: `- - ‖ (y)` — reaches the
    ///   SAME key at depth d+1, where `paren` still has budget and `(y)`
    ///   parses fine.
    ///
    /// With `k = MAX_CATEGORY_DEPTH - 3` leading parens to burn the
    /// budget down to exactly that boundary, the pre-fix cache poisons
    /// `double`'s reach with `unary`'s depth-capped `Err` and the whole
    /// (perfectly parseable) input is rejected. Post-fix the tainted
    /// entry is never inserted, `double` re-parses at its own shallower
    /// depth, and the parse succeeds.
    #[test]
    fn a_depth_capped_subparse_never_poisons_a_shallower_reach_of_the_same_key() {
        in_worker("depth-cap taint", || {
            let mut b = SnapshotBuilder::new();
            b.category("e", LeadingIdentBehavior::Default);
            b.leading2("e", "atom", MAX_PREC, Prim::Ident);
            b.leading2(
                "e",
                "paren",
                MAX_PREC,
                seq([sym("("), cat("e", 0), sym(")")]),
            );
            // Registration order matters: `longest_match` attempts
            // candidates in order, so the DEEP path (`unary`, which
            // recurses once more before reaching the shared key) runs
            // first and is the one that would populate the cache with a
            // depth-capped result.
            b.leading2("e", "unary", MAX_PREC, seq([sym("-"), cat("e", 0)]));
            b.leading2(
                "e",
                "double",
                MAX_PREC,
                seq([sym("-"), sym("-"), cat("e", 0)]),
            );
            let snap = b.finish();

            let k = MAX_CATEGORY_DEPTH as usize - 3;
            let src = "(".repeat(k) + "- - (y)" + &")".repeat(k);

            // (1) The whole (perfectly parseable) input must parse at
            //     all. Pre-fix this is an `Err`: `double`'s reach of the
            //     shared key hits `unary`'s cached, depth-capped failure.
            let mut ps = Ps::new(&src, &snap);
            let r = ps.run(&Prim::Category {
                name: "e".to_string(),
                rbp: 0,
            });
            assert!(
                r.is_ok(),
                "valid input REJECTED: a depth-capped sibling attempt \
                 poisoned the cache entry for a shallower reach of the \
                 same (pos, category, rbp) key"
            );

            // (2) …and with exactly the shape a fresh parse produces.
            let mut expected = format!("(double '-' '-' {})", "(paren '(' (atom y) ')')");
            for _ in 0..k {
                expected = format!("(paren '(' {expected} ')')");
            }
            assert_eq!(parse_cat(&snap, &src), expected);
        });
    }

    /// Task 11b review WAVE 2, CRITICAL 1 (reopened): the depth taint must
    /// also propagate through a cache **HIT**. Keying tainted entries by
    /// headroom is not enough on its own — the taint counter (`cap_hits`)
    /// used to be bumped only where the cap arm *fires*, which is only
    /// reachable on a MISS. A call that merely *inherits* a capped
    /// sub-result by replaying a `depth_headroom: Some(_)` entry therefore
    /// exited with `cap_hits` unmoved and got filed under `None` — i.e.
    /// advertised as valid at ANY `cat_depth` while carrying a depth-cap
    /// artifact inside it. Replaying THAT at a shallower depth is the
    /// original Critical 1 all over again, one level up.
    ///
    /// The shape below (the reviewer's traced path, as a toy grammar) is
    /// deliberately NOT the one
    /// `a_depth_capped_subparse_never_poisons_a_shallower_reach_of_the_same_key`
    /// exercises: there, the poisoned key is reached by a *fresh* deeper
    /// parse. Here it is reached by a *hit*, and that test passes even with
    /// the hit-path bump removed.
    ///
    /// - `lo`/`hi` are two leading candidates on the same first token `#`,
    ///   differing only in the `rbp` they hand to their inner category call
    ///   (`0` vs `MAX_PREC` — exactly `builtin/term.rs`'s commonplace
    ///   `cat("term", 0)`-vs-`cat("term", MAX_PREC)` split). Both therefore
    ///   run at the SAME position and the SAME `cat_depth`, under DIFFERENT
    ///   keys, and both reach the identical inner key `K` = the paren
    ///   chain's second level.
    /// - `lo` is registered first, so it runs first and computes `K` fresh.
    ///   The paren chain is sized so that at `lo`'s depth the cap fires
    ///   inside it ⇒ `K` is stored `Some(h)`, `E₀` (`lo`'s inner call) is
    ///   correctly tainted, and `lo` fails.
    /// - `hi` then runs at the same position/depth, reaches `K` ⇒ **cache
    ///   HIT on a `Some(h)` entry**. Pre-fix: no taint ⇒ `E₁` (`hi`'s inner
    ///   call) is filed under `None` while carrying `K`'s capped failure.
    /// - `unary`/`double` put the whole `#…` construct at two `cat_depth`s
    ///   one level apart (`unary` twice = deep, `double` once = shallow).
    ///   `lo` can never succeed (it demands a trailing `@` the input does
    ///   not have), so at the shallow depth the parse hinges entirely on
    ///   `hi` — which pre-fix takes the poisoned `None` hit and rejects
    ///   input that a fresh parse at that depth parses cleanly.
    #[test]
    fn a_cache_hit_on_a_depth_capped_entry_taints_its_ancestors_too() {
        in_worker("depth-cap taint through a cache hit", || {
            let mut b = SnapshotBuilder::new();
            b.category("e", LeadingIdentBehavior::Default);
            b.leading2("e", "atom", MAX_PREC, Prim::Ident);
            b.leading2(
                "e",
                "paren",
                MAX_PREC,
                seq([sym("("), cat("e", 0), sym(")")]),
            );
            b.leading2("e", "unary", MAX_PREC, seq([sym("-"), cat("e", 0)]));
            b.leading2(
                "e",
                "double",
                MAX_PREC,
                seq([sym("-"), sym("-"), cat("e", 0)]),
            );
            // Registration order matters: `lo` must run (and populate the
            // cache) before `hi` reaches the same inner key.
            b.leading2("e", "lo", MAX_PREC, seq([sym("#"), cat("e", 0), sym("@")]));
            b.leading2("e", "hi", MAX_PREC, seq([sym("#"), cat("e", MAX_PREC)]));
            let snap = b.finish();

            // Depth budget: `#`'s inner call sits at `cat_depth` 3 down the
            // `unary`+`unary` path and at 2 down the `double` path. One
            // paren level costs exactly one `cat_depth`, and the innermost
            // `y` needs one more, so `m` parens make the deep path's
            // innermost call land at `3 + m` and the shallow path's at
            // `2 + m`. `m = MAX_CATEGORY_DEPTH - 3` therefore trips the cap
            // on the deep path (`3 + m == MAX_CATEGORY_DEPTH`) and clears
            // it by exactly one level on the shallow path.
            let m = MAX_CATEGORY_DEPTH as usize - 3;
            let src = "- - #".to_string() + &"(".repeat(m) + "y" + &")".repeat(m);

            let mut ps = Ps::new(&src, &snap);
            let r = ps.run(&Prim::Category {
                name: "e".to_string(),
                rbp: 0,
            });
            assert!(
                r.is_ok(),
                "valid input REJECTED: a cache HIT on a depth-capped entry \
                 failed to taint its ancestor, so the ancestor was filed as \
                 depth-independent and poisoned a shallower reach of its key"
            );

            let mut inner = "(atom y)".to_string();
            for _ in 0..m {
                inner = format!("(paren '(' {inner} ')')");
            }
            let expected = format!("(double '-' '-' (hi '#' {inner}))");
            assert_eq!(parse_cat(&snap, &src), expected);
        });
    }

    /// Task 11b regression: the general shape that exploded
    /// exponentially before `category()` memoization — N leading
    /// candidates sharing the identical `"("` first-token slot, each
    /// independently recursing into the SAME category at the SAME
    /// inner position (`category`'s own doc comment; the real builtin
    /// grammar's `register_paren_family` — `paren`/`tuple`/
    /// `typeAscription` — is a 3-candidate instance of exactly this).
    /// 6 candidates nested to depth 20 is 6^20 ≈ 3.7e15 unmemoized
    /// attempts, i.e. this test would never finish without the cache;
    /// with it, every sibling past the first at a given nesting level
    /// is an O(1) hit, so the whole parse is Θ(N·depth). The un-memoized
    /// cost is *infinite* for practical purposes, so the bound can't be
    /// asserted after the fact (`elapsed < BUDGET` past a call that never
    /// returns never runs — Task 11b review, Important 3): `in_worker`
    /// runs the parse on its own thread and gives up on it, failing the
    /// test, if it is still going after the budget. Plus an exact
    /// expected-shape assertion (not just "didn't hang").
    #[test]
    fn pathological_alternation_fanout_is_bounded_by_the_category_cache() {
        const N: usize = 6;
        const DEPTH: usize = 20;
        let got = in_worker("6-way fanout at depth 20", || {
            let mut b = SnapshotBuilder::new();
            b.category("e", LeadingIdentBehavior::Default);
            b.leading2("e", "atom", MAX_PREC, Prim::Ident);
            for i in 0..N {
                b.leading2(
                    "e",
                    &format!("paren{i}"),
                    MAX_PREC,
                    seq([sym("("), cat("e", 0), sym(")")]),
                );
            }
            let snap = b.finish();
            let src = "(".repeat(DEPTH) + "x" + &")".repeat(DEPTH);
            parse_cat(&snap, &src)
        });
        // All N candidates are structurally identical (differ only in
        // kind name), so every level is a genuine tie: `longest_match`
        // picks the FIRST-registered winner ("paren0") deterministically,
        // making the resulting shape fully predictable.
        let mut expected = "(atom x)".to_string();
        for _ in 0..DEPTH {
            expected = format!("(paren0 '(' {expected} ')')");
        }
        assert_eq!(got, expected);
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
        b.category("c", LeadingIdentBehavior::Default);
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
    fn trailing_many_finding_nothing_after_a_real_item_does_not_leak_as_phantom_consumption() {
        // Task 8 wave 2 review fix. A trailing production whose body
        // ends in `many(seq([CheckWsBefore, CheckColGt, cat(..)]))` —
        // the exact shape `Term.pipeProj`'s `many argument`
        // (`builtin/term/term_app.rs`) and `Term.app`'s own `many1
        // argument` both have — must NOT hard-fail just because the
        // loop's NEXT attempt, after a real match, lands on a token
        // that dispatches to nothing in this category.
        //
        // Before this fix, `CheckWsBefore`/`CheckColGt` (and the
        // category trailing loop's own dispatch lookahead) used the
        // COMMITTING `peek_significant`, which permanently skips
        // whitespace/comments even when nothing ultimately qualifies.
        // `many_impl`'s `consumed_since` check then couldn't tell that
        // leaked trivia-skip apart from real progress: a clean,
        // zero-net-progress stop looked like a hard, consuming failure,
        // which `longest_match`'s enclosing restore then discarded
        // WHOLESALE — losing the already-successfully-matched first
        // item too, not just the failed second attempt.
        //
        // `Term.app`'s own tests didn't catch this because its
        // argument's LAST step is always a full `termParser argPrec`
        // CATEGORY RECURSION, whose own (separate) trailing loop
        // happens to eat the following trivia while finding nothing
        // further qualifies, before `many1` ever takes its next-
        // iteration savepoint — accidentally masking the bug. This
        // toy grammar reproduces it directly with a BARE trailing
        // token match (no nested category recursion) as the item,
        // matching `pipeProj`'s `fieldIdx <|> rawIdent` alternative.
        let mut b = SnapshotBuilder::new();
        b.category("c", LeadingIdentBehavior::Default);
        b.leading2("c", "lit", MAX_PREC, Prim::Ident);
        b.trailing2(
            "c",
            "wrap",
            0,
            0,
            seq([
                sym("!"),
                many(seq([Prim::CheckWsBefore, Prim::CheckColGt, cat("c", 0)])),
            ]),
        );
        let snap = b.finish();

        // "y" is matched as the loop's one item; the following "?"
        // (across a newline) dispatches to nothing this category
        // recognizes as either leading or trailing — the loop must
        // stop cleanly, keeping "y" rather than discarding the whole
        // `wrap` (which would leave `x` bare and `! y` as an
        // unresolved leftover, or — pre-fix — a hard parse error).
        assert_eq!(
            parse_cat(&snap, "x ! y\n?"),
            "(wrap (lit x) '!' (null (lit y)))"
        );
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
        b.category("c", LeadingIdentBehavior::Default);
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
        b.category("c", LeadingIdentBehavior::Default);
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

    /// `render_error` (task-11-brief.md Step 4): 1-based line/col,
    /// stable-coded `error[Exxxx]: msg` rendering. An error at the
    /// start of line 3 must render `3:1: …`.
    #[test]
    fn render_error_reports_one_based_line_and_column() {
        let src = "def a := 1\ndef b := 2\n???\n";
        let at = src.find("???").unwrap() as u32;
        let e = ParseError {
            code: "E0301",
            span: (at, at),
            msg: "unexpected input; expected one of: <command>".to_string(),
        };
        assert_eq!(
            render_error(src, &e),
            "3:1: error[E0301]: unexpected input; expected one of: <command>"
        );
    }

    /// M3a final-review Minor finding (c): `recover_command` used to
    /// hand-roll its E0301 message as `format!("...expected one of:
    /// {}", expected.join(", "))`, which renders a dangling "expected
    /// one of: " with nothing after it whenever the furthest-failure
    /// expected set is empty. It now reuses `push_furthest_error`'s
    /// already-guarded construction instead. Drive `recover_command` on
    /// a freshly constructed `Ps`, where `furthest_pos`/
    /// `furthest_expected` are still at their `Ps::new` defaults (`0`,
    /// `[]`) because no `fail_expecting` call has run yet — so the
    /// expected set really is empty when the diagnostic is rendered —
    /// and assert the message is the guarded fallback, never a dangling
    /// join.
    #[test]
    fn recover_command_never_emits_dangling_expected_one_of() {
        let mut k = KindInterner::new();
        let table = TokenTable::default();
        let mut ps = Ps::new_for_test("stray tokens here", table, &mut k);
        ps.recover_command();
        let errors = ps.errors();
        assert_eq!(errors.len(), 1, "recover_command records exactly one E0301");
        assert_eq!(errors[0].code, "E0301");
        assert!(
            !errors[0].msg.contains("expected one of: "),
            "dangling \"expected one of: \" with nothing after it: {:?}",
            errors[0].msg
        );
        assert_eq!(
            errors[0].msg, "unexpected input",
            "empty expected set must render push_furthest_error's guarded fallback"
        );
    }

    /// Task 11 Step 3's targeted regression: an unterminated string
    /// literal must surface exactly ONE `E0302`, never duplicated by a
    /// `longest_match`/speculative re-lex of the same offset.
    /// `longest_match` (this file) already isolates each candidate's
    /// errors behind its own `restore(sp)` and only splices the WINNING
    /// candidate's own error suffix back into `Ps::errors` — verified
    /// empirically (task-11 report) across `longest_match`-heavy shapes
    /// (tuples, lists, struct instances, `match`, binary operators) with
    /// no duplicate surfacing in any of them; this test pins the
    /// brief's own literal repro so a future regression here is caught.
    #[test]
    fn unterminated_string_reports_e0302_exactly_once() {
        let snap = crate::builtin::snapshot();
        let src = "def x := \"open";
        let r = parse_module(src, &snap);
        assert_eq!(r.tree.text(), src, "round-trip failed");
        let e0302: Vec<_> = r.errors.iter().filter(|e| e.code == "E0302").collect();
        assert_eq!(e0302.len(), 1, "{:?}", r.errors);
    }

    /// A `«term_⊕_»` infixl on `⊕`, `term` category, prec 65/lhs_prec 65
    /// — same shape/fields as `grammar::overlay::tests::
    /// register_adds_token_kind_and_trailing_entry` (Task 5 Step 1),
    /// EXCEPT the `body`: that test only ever exercises `Overlay::
    /// register`'s bookkeeping (never runs a parse), so its body —
    /// `seq([cat("term", 66), sym("⊕"), cat("term", 66)])` — re-parses a
    /// SECOND leading term ahead of the `⊕` symbol, which is not how a
    /// trailing production is shaped (the Pratt loop already has the lhs
    /// — see every base `trailing2` registration in `builtin/term.rs`,
    /// e.g. `Term.arrow`: `seq([sym("→"), cat("term", 25)])`, operator
    /// then rhs, never lhs again). Used unmodified, that body can never
    /// actually match (its own leading `cat("term", 66)` would need to
    /// parse starting AT `⊕`, which has no leading production of its
    /// own) — so THIS helper fixes the body to the real trailing shape
    /// or `installed_overlay_parses_new_infix` below could never pass.
    fn sum_spec() -> NotationSpec {
        NotationSpec {
            category: "term".into(),
            kind_name: "«term_⊕_»".into(),
            leading: false,
            prec: 65,
            lhs_prec: Some(65),
            tokens: vec!["⊕".into()],
            body: seq([sym("⊕"), cat("term", 66)]),
        }
    }

    /// M3b1 Task 6 Step 1: a manually-installed overlay actually changes
    /// parsing. The base grammar can't parse `a ⊕ b` as one term — `⊕`
    /// is unknown to it (lexes as `ErrorTok`, no dispatch entry anywhere)
    /// — so without the overlay this would fail to consume `⊕ b` at all;
    /// with `sum_spec()` installed, `a ⊕ b` groups as one `«term_⊕_»`
    /// node, proving all three read points (munch, dispatch, kind
    /// naming) actually route through `self.overlay`.
    #[test]
    fn installed_overlay_parses_new_infix() {
        let base = crate::builtin::snapshot();
        let mut ov = Overlay::new(&base);
        ov.register(sum_spec());
        let src = "prelude\n#check a ⊕ b\n";
        let r = parse_module_with_overlay(src, &base, ov);
        assert_eq!(r.tree.text(), src, "round-trip failed");
        assert!(
            r.tree
                .root()
                .descendants()
                .any(|n| r.tree.kinds.name(n.kind()) == "«term_⊕_»"),
            "no «term_⊕_» node in the tree: {:#?}",
            r.tree.root()
        );
    }

    /// Companion to the above: an EMPTY overlay (the default `Ps::new`
    /// state) must NOT change parsing — `⊕` stays unrecognized, exactly
    /// as in M3a. Not a full parse-equivalence check (that's the whole
    /// crate's existing suite, run as this task's regression gate); this
    /// just pins the one new behavior (`⊕` specifically) the empty case
    /// must still reject, so a future accidental "always consult overlay
    /// candidates" bug (e.g. forgetting the `category_delta(name)` is
    /// `None` check) would be caught right next to the positive case.
    #[test]
    fn empty_overlay_still_rejects_the_new_infix() {
        let base = crate::builtin::snapshot();
        let src = "prelude\n#check a ⊕ b\n";
        let r = parse_module(src, &base);
        assert!(
            !r.errors.is_empty(),
            "expected a parse error for the unknown `⊕` with no overlay installed"
        );
        assert!(!r
            .tree
            .root()
            .descendants()
            .any(|n| r.tree.kinds.name(n.kind()) == "«term_⊕_»"));
    }

    /// M3b1 Task 7 Step 1: the command loop itself grows the overlay —
    /// no manually pre-seeded `Overlay` (unlike the pair above, which
    /// exercise `parse_module_with_overlay`). An `infixl:65 " ⊕ " =>
    /// Sum` command on line 2 must be LIVE for the `#check a ⊕ b` on
    /// line 3, via plain `parse_module`.
    #[test]
    fn same_file_notation_is_live_on_the_next_line() {
        let snap = crate::builtin::snapshot();
        let src = "prelude\ninfixl:65 \" ⊕ \" => Sum\n#check a ⊕ b\n";
        let r = crate::parse_module(src, &snap);
        assert_eq!(r.tree.text(), src);
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        // the #check uses the just-declared notation
        assert!(
            r.tree
                .root()
                .descendants()
                .any(|n| r.tree.kinds.name(n.kind()) == "«term_⊕_»"),
            "notation not live on next line"
        );
    }

    /// Review follow-up (Issue 1, perf): `command_may_grow_grammar`'s
    /// own classification, exercised directly against real successful
    /// `Category { name: "command", .. }` parses — mirrors
    /// `run_module`'s own loop shape (peek header, then per command:
    /// save, run the category, classify) without going through the
    /// full `parse_module` + `derive` pipeline. A `mixfix` AND a
    /// `notation` command must both classify as build-eligible; a
    /// `def` and a `#check` (representative of "everything else") must
    /// both classify as skip — proving the peek neither wrongly skips
    /// a real notation/mixfix command nor wrongly builds for an
    /// ordinary one.
    #[test]
    fn command_may_grow_grammar_classifies_notation_and_mixfix_true_others_false() {
        let snap = crate::builtin::snapshot();
        let module = snap
            .kinds()
            .lookup("module")
            .expect("interned by builtin::snapshot");
        let src = "prelude\ninfixl:65 \" ⊕ \" => Sum\nnotation:70 a \" ⊗ \" b => Prod a b\ndef bar := 1\n#check bar\n";
        let mut ps = Ps::new(src, &snap);
        ps.start(module);
        let header = snap
            .header_prim()
            .expect("builtin::snapshot() always sets a header");
        ps.run(&header).expect("header never fails");

        let mut classifications = Vec::new();
        loop {
            let (t, _at) = ps.peek_significant();
            if t.kind == crate::lex::TokenKind::Eof {
                break;
            }
            let sp = ps.save();
            let r = ps.run(&Prim::Category {
                name: "command".into(),
                rbp: 0,
            });
            assert!(
                r.is_ok(),
                "every command in this fixture must parse cleanly: {r:?}"
            );
            classifications.push(ps.command_may_grow_grammar(sp.events));
        }
        assert_eq!(
            classifications,
            vec![true, true, false, false],
            "expected [infixl=mixfix, notation, def=skip, #check=skip]"
        );
    }

    /// M3b1 Task 9 Step 1: a malformed `infixl` (missing the mandatory
    /// `=> rhs` tail) must register NOTHING — the overlay stays
    /// unmutated — and the command loop must resync cleanly so the
    /// `def good` after it still parses as a real declaration.
    ///
    /// `⊕` is fine to reuse here (unlike a real oracle-compared
    /// fixture — see `NotationBadResync.lean`'s own doc comment on why
    /// IT needed a novel `⧉` instead): this is a leanr-internal `parse_module`
    /// unit test, never diffed against a `lean --run dump_syntax.lean`
    /// dump, so Init's own pre-existing `infixr:30 " ⊕ " => Sum`
    /// declaration (which this crate's builtin snapshot doesn't even
    /// model) has no bearing on it.
    ///
    /// TDD per the task brief: run BEFORE Task 9's Step 3 guard existed
    /// — PASSED ALREADY (recorded in task-9-report.md), because Task
    /// 7's loop already gates `derive`/`register` behind the clean
    /// `Ok(())` command-loop arm only (never the `Err`/zero-progress
    /// resync arms, both of which `restore(&sp)` first): the missing
    /// `=> Sum` tail makes `sym("=>")` fail INSIDE the `mixfix` leading
    /// production's own `Prim::Seq`, which has no per-slot recovery of
    /// its own (a consuming failure inside `Seq`/`OrElse`/`Optional`
    /// always propagates up as a hard `Err`, never a partial `Ok` with
    /// a `<missing>`/`<error>` node spliced in) — so the WHOLE `mixfix`
    /// candidate fails, `category("command", 0)` finds no leading
    /// winner, and the outer command-loop match takes the `Err(_)` arm
    /// (restore + `recover_command`), never reaching `derive`/
    /// `register` at all. Kept as a regression test regardless of
    /// whether it needed the Step 3 guard to pass, per the brief.
    #[test]
    fn malformed_notation_registers_nothing_and_resyncs() {
        let snap = crate::builtin::snapshot();
        // missing `=> rhs` — malformed
        let src = "prelude\ninfixl:65 \" ⊕ \"\ndef good := 1\n";
        let r = crate::parse_module(src, &snap);
        assert_eq!(r.tree.text(), src); // still lossless
        assert!(!r.errors.is_empty()); // the bad line errored
                                       // the good def after it parsed as a real declaration, not swallowed
        assert!(r
            .tree
            .root()
            .children()
            .any(|c| r.tree.kinds.name(c.kind()) == "Lean.Parser.Command.declaration"));
        // ⊕ was NOT registered (no «term_⊕_» kind anywhere)
        assert!(!r
            .tree
            .root()
            .descendants()
            .any(|n| r.tree.kinds.name(n.kind()) == "«term_⊕_»"));
    }

    /// M3b2a Task 4: `parse_header_imports` — a header-only parse, never
    /// touching the command loop (Step 4's `#check 1` after the imports
    /// proves this: if it were parsed as a command too and failed, that
    /// wouldn't show up here either way, but a whole-module parse of
    /// malformed input further down WOULD panic/hang if this secretly
    /// delegated to `parse_module`'s command loop instead of stopping at
    /// the header).
    #[test]
    fn header_imports_are_extracted() {
        assert_eq!(
            parse_header_imports("import Foo\nimport Foo.Bar.Baz\n#check 1\n"),
            vec!["Foo".to_string(), "Foo.Bar.Baz".to_string()]
        );
        assert_eq!(parse_header_imports("#check 1\n"), Vec::<String>::new());
        assert_eq!(
            parse_header_imports("prelude\n#check 1\n"),
            Vec::<String>::new()
        );
        // Malformed header: never panic, best-effort.
        let _ = parse_header_imports("import \u{0}\u{0}");
    }
}
