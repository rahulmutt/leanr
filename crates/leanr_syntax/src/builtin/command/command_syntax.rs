//! `syntax`-family command SHAPES (M3b2b Task 6 — pure M3a-style
//! grammar-production porting, exactly like M3b1's `command_notation.
//! rs`, whose module doc states the same discipline: no registration/
//! overlay logic, no derivation — those are Tasks 7-8). ORACLE-PORT
//! `Lean/Parser/Syntax.lean` (the `stx` category's own item grammar —
//! `Syntax.paren`/`.cat`/`.unary`/`.binary`/`.sepBy`/`.sepBy1`/`.atom`/
//! `.nonReserved` — plus the `Command` namespace's `syntax`/
//! `syntaxAbbrev`/`syntaxCat`/`macro_rules`/`macro`) at the pinned
//! toolchain (`~/.elan/toolchains/*/lib/lean4/library/Lean/Parser/
//! Syntax.lean`, v4.32.0-rc1).
//!
//! **The quantifier-suffix trio (`+`/`?`/`,*`) is a genuine, forced
//! divergence from that source file**: `Lean/Parser/Syntax.lean` itself
//! defines ONLY the 8 productions above (plus `unicodeAtom`, unexercised
//! — no fixture needs it). The `p+`/`p*`/`(p)?`/`p,*`/`p,+` shorthand
//! sugar used pervasively in real `syntax` declarations (including this
//! task's own `StxShapes.lean`) is instead bootstrapped in
//! `Init/Notation.lean:171-232` via ordinary `syntax`/`macro_rules`
//! commands targeting the `stx` category ITSELF (`stx`'s own dynamic
//! `@[stx_parser]` extensibility, `Syntax.lean:18`) — i.e. these are
//! not `@[builtin_syntax_parser]`-compiled productions at all, they are
//! Init-library self-hosting. Ported here anyway because the STEP 1
//! dump is arbiter and pins them regardless of provenance (fresh probe,
//! `.scratch_probe/probe4.lean`, task-6 report): `many_of term+`'s
//! second item dumps as
//! ```text
//! {"k":"«stx_+»","c":[
//!   {"k":"Lean.Parser.Syntax.cat","c":[{"i":"term"},{"k":"null","c":[]}]},
//!   {"a":"+"}
//! ]}
//! ```
//! — a TRAILING production (`Init/Notation.lean:171`: `syntax:arg
//! stx:max "+" : stx`, i.e. a left-recursive `stx:max` reference makes
//! this a `stx`-category trailing entry, `lhs_prec = MAX_PREC`, own
//! registered `prec = ARG_PREC` from the `:arg` precedence annotation)
//! wrapping the already-parsed lhs plus a bare `"+"` atom, 2 children
//! total. `opt_of (term)?`'s dump is the same shape with kind `stx_?`
//! (no guillemets — unlike `«stx_+»`/`«stx_,*»`, `?` IS a legal ident
//! TRAILING character in Lean's `Name.toString`, so it never needs
//! escaping; `+`/`,*` are not, hence the guillemets are part of the
//! LITERAL kind-name string, transcribed verbatim below) wrapping
//! `[Syntax.paren, {"a":"?"}]`. `probe! term,*`'s dump is `«stx_,*»`
//! wrapping `[Syntax.cat, {"a":",*"}]` — `",*"` is already a registered
//! snapshot-wide token (`builtin/mod.rs`'s antiquot-splice-suffix
//! registration; same literal text, unrelated grammar position, one
//! token-table entry per the tokenizer's single global maximal-munch
//! table). `,+`/`<|>`/`!` (`Init/Notation.lean:232-258`) are NOT
//! ported: no fixture line exercises them (same "don't fabricate
//! unexercised productions" discipline as `term_quot.rs`'s skipped
//! `Term.precheckedQuot`/`Tactic.quotSeq`).
//!
//! **`stx` category's own `LeadingIdentBehavior`**: `Syntax.lean:17`'s
//! registration, `registerBuiltinParserAttribute \`builtin_syntax_parser
//! ``Category.stx .both`, is EXPLICIT `.both` — pinned as
//! `LeadingIdentBehavior::Both` in `builtin/mod.rs::builder()` (NOT the
//! `#[default]` `Default` the brief's skeleton placeholder showed;
//! that placeholder is corrected here per its own instruction to read
//! the behavior off the oracle's registration call site).
//!
//! **Command-side `macroArg` is NOT the same node as `term_pragma.rs`'s
//! `macro_arg`/`macro_dollar_arg`/`macro_last_arg`** (despite the
//! shared bare name) — a real check, not an assumption: `term_pragma.
//! rs`'s own doc comment pins `Term.lean`'s `macroArg := termParser
//! maxPrec` as "a plain alias, NOT itself a `leading_parser` (no node
//! wrap)", i.e. it never appears as a `"k"` entry in any dump at all.
//! `Lean/Parser/Syntax.lean:115-116`'s `Command.macroArg := leading_
//! parser optional (atomic (ident >> checkNoWsBefore ":")) >>
//! syntaxParser argPrec` genuinely IS a `leading_parser` (self-wraps),
//! confirmed against the fresh dump below (`Lean.Parser.Command.
//! macroArg`, 2 children each). Since the two `macroArg`s don't even
//! share a KIND (one has none), there is no shared node to hoist —
//! this file gets its own private `macro_arg` helper, distinct from
//! (and never colliding with, different module) `term_pragma.rs`'s.
//!
//! **Fresh oracle dumps** (`.scratch_probe/probe4.lean` — stx items —
//! and `probe5.lean` — `macro_rules`/`macro`, both regenerated via
//! `dump_syntax_elab.lean`, task-6 report) pin every shape below;
//! excerpts:
//! ```text
//! `syntax:65 "probe" term : term` → Lean.Parser.Command.syntax{
//!   null(doc), null(attrs), Term.attrKind{null}, "syntax",
//!   null(precedence{":", num{"65"}}), null(namedName), null(namedPrio),
//!   null([Syntax.atom{str{"probe"}}, Syntax.cat{ident"term", null}]),
//!   ":", ident"term" }                                    -- 10 children
//! `syntax (name := probed) "probe!" term,* : term` confirms optNamedName's
//!   populated shape (Command.namedName{"(", "name", ":=", ident"probed",
//!   ")"}) and the `«stx_,*»` trailing wrap above.
//! `declare_syntax_cat gadget (behavior := symbol)` → Lean.Parser.
//!   Command.syntaxCat{ null(doc), "declare_syntax_cat", ident"gadget",
//!   null(["(", "behavior", ":=", Command.catBehaviorSymbol{"symbol"},
//!   ")"]) }                                                -- 4 children
//! `syntax myNum := num` → Lean.Parser.Command.syntaxAbbrev{ null(doc),
//!   null(visibility), "syntax", ident"myNum", ":=",
//!   null([Syntax.cat{ident"num", null}]) }                 -- 6 children
//! `macro_rules (kind := myKind) | \`(probe $x) => \`(f $x)` (probe5) →
//!   Lean.Parser.Command.macro_rules{ null(doc), null(attrs),
//!   Term.attrKind{null}, "macro_rules",
//!   null(["(", "kind", ":=", ident"myKind", ")"]),
//!   Term.matchAlts{...} }                                  -- 6 children
//!   (bare `macro_rules |` — no `(kind := ..)` — confirms the empty
//!   `null(optKind)` case, 0 children.) The `Term.matchAlt`'s rhs is a
//!   PLAIN `cat("term", 0)`: quotations parse via the "term" category
//!   already (`term_quot.rs`, `Lean.Parser.Term.quot` at MAX_PREC), so
//!   `Term.matchAlts`/`Term.matchAlt` (`term.rs`, already ported for
//!   `match`) are reused UNCHANGED, no `macro_rules`-specific variant
//!   needed.
//! `macro:65 (name := tripleName) (priority := 10) "triple" x:term :
//!   term => \`(f $x $x $x)` (probe5) → Lean.Parser.Command.macro{
//!   null(doc), null(attrs), Term.attrKind{null}, "macro",
//!   null(precedence), null(namedName), null(namedPrio),
//!   null([macroArg{null, Syntax.atom{str{"triple"}}},
//!         macroArg{null["x", ":"], Syntax.cat{ident"term", null}}]),
//!   Command.macroTail{ ":", ident"term", "=>",
//!     Command.macroRhs{ Term.quot{...} } } }                -- 9 children
//!   (`macroArg`'s own 2 children: `optional(atomic(ident >> ":"))` —
//!   a bare `null` wrapping flat `[ident, ":"]` when present, empty
//!   `null` when absent — then the `syntaxParser argPrec` item itself.)
//! ```
//! `f $x`/`f $x $x`/`f $x $x $x` (this file's own fixture substitution
//! for the brief's draft `$x + 1`/`$x + $x`, documented in the fixture
//! authoring notes — see `tests/fixtures/syntax/QuotMacroRules.lean`):
//! `Term.app` (already ported, `term.rs`) handles the application chain
//! with no new work here; the substitution changes nothing about the
//! `macro_rules`/`macro` SHAPES this file registers.
//!
//! `suppressInsideQuot` (wrapping `macro_rules`/`macro`'s WHOLE body in
//! the oracle) is a success-path no-op here (it only suppresses the
//! production from being tried while ALREADY inside an active `` `(..)
//! `` quotation — no fixture nests a `macro_rules`/`macro` inside one) —
//! skipped, same "semantic-only wrapper, doesn't reshape a successful
//! parse" treatment `term.rs`'s `checkStackTop`/`command_notation.rs`'s
//! malformed-input notes already establish. `withoutPosition` throughout
//! (`paren`/`unary`/`binary`/`sepBy`/`sepBy1`'s bodies, `macroRhs`'s
//! `withPosition`) is likewise omitted — this engine has no
//! `WithPosition` frame to be transparent through unless one is
//! explicitly pushed, and no fixture forces a column check that would
//! prove otherwise (same reasoning `term_quot.rs`'s module doc already
//! gives for the four quotation productions).

use super::super::attr::{attr_kind, attributes};
use super::super::command::{doc_comment, named_name, named_prio, nd, precedence, visibility};
use crate::builtin::term::match_alts;
use crate::grammar::*;

/// The `stx` category's own item grammar (`Lean/Parser/Syntax.lean`'s
/// `Syntax` namespace) plus the Init-bootstrapped quantifier-suffix
/// trio — see module doc for the full oracle-dump citations pinning
/// every shape below.
fn register_stx_items(b: &mut SnapshotBuilder) {
    // Syntax.paren := leading_parser "(" >> withoutPosition (many1
    // syntaxParser) >> ")"` — bare `leading_parser` (no `:N`), MAX_PREC.
    b.leading2(
        "stx",
        "Lean.Parser.Syntax.paren",
        MAX_PREC,
        seq([sym("("), many1(cat("stx", 0)), sym(")")]),
    );

    // Syntax.cat := ident >> optPrecedence — `precedence` hoisted to
    // `command.rs` (shared with `command_notation.rs`'s `notation`/
    // `mixfix`). UNLIKE `command_notation.rs`'s own `opt(precedence(b))`
    // call sites (no `atomic` there), THIS one needs the real oracle's
    // full `optPrecedence := optional (atomic «precedence»)` wrap —
    // found the hard way, not assumed: `syntax num : widgetish` (a
    // bare-ident stx item directly followed by the ENCLOSING `syntax`
    // command's own " : " target-category separator) hard-failed
    // without it. Once `Prim::Ident` consumes "num", `opt(precedence)`
    // sees the very next token IS a literal `":"` and commits to
    // `precedence`'s `":" >> NumLit`; without `atomic` scoping the
    // WHOLE clause, a `NumLit` failure (here, "widgetish" — an ident,
    // not a number) propagates as a hard parse error instead of
    // backtracking to "no precedence present", stranding the outer
    // command's own `":"` with no candidate left to consume it.
    // `command_notation.rs`'s own `notation`/`identPrec` call sites
    // never hit this because nothing else in THEIR grammars puts a
    // bare, non-precedence `":"` immediately after an optional-
    // precedence slot — a real, narrower ambiguity than this file's.
    //
    // Deliberate omission: the oracle's `optPrecedence` is ONE shared
    // `optional (atomic precedence)` def, used uniformly at every
    // optional-precedence call site. This port applies the `atomic`
    // wrap only here, where the ambiguity above forces it, and leaves
    // `notation`/`identPrec`'s own `opt(precedence(b))` un-atomic —
    // `atomic` only changes BACKTRACK behavior on a failed inner parse,
    // never the success-path tree shape, so this divergence produces
    // byte-identical trees on any clean input; only a pathological
    // failure shaped like `syntax num : widgetish`'s (absent from
    // `notation`/`identPrec`'s own grammars) could tell the two apart.
    let prec = atomic(precedence(b));
    b.leading2(
        "stx",
        "Lean.Parser.Syntax.cat",
        MAX_PREC,
        seq([Prim::Ident, opt(prec)]),
    );

    // Syntax.unary := ident >> checkNoWsBefore >> "(" >> withoutPosition
    // (many1 syntaxParser) >> ")"` — e.g. `optional(term)`,
    // `many1(term)`. `checkNoWsBefore` is zero-width (no json child).
    b.leading2(
        "stx",
        "Lean.Parser.Syntax.unary",
        MAX_PREC,
        seq([
            Prim::Ident,
            Prim::CheckNoWsBefore,
            sym("("),
            many1(cat("stx", 0)),
            sym(")"),
        ]),
    );

    // Syntax.binary := ident >> checkNoWsBefore >> "(" >> withoutPosition
    // (many1 syntaxParser >> ", " >> many1 syntaxParser) >> ")"` — e.g.
    // `orelse(term, num)`.
    b.leading2(
        "stx",
        "Lean.Parser.Syntax.binary",
        MAX_PREC,
        seq([
            Prim::Ident,
            Prim::CheckNoWsBefore,
            sym("("),
            many1(cat("stx", 0)),
            sym(","),
            many1(cat("stx", 0)),
            sym(")"),
        ]),
    );

    // Syntax.sepBy/.sepBy1 := "sepBy("/"sepBy1(" (fused, space-free
    // tokens) >> withoutPosition (many1 syntaxParser >> ", " >> strLit
    // >> optional (", " >> many1 syntaxParser) >> optional (", " >>
    // nonReservedSymbol "allowTrailingSep")) >> ")"`. The custom-`psep`
    // and `allowTrailingSep` optionals are real, transcribed shapes but
    // UNEXERCISED by any fixture line (both fixture lines use the
    // 2-arg form) — same "real, always-empty optional" idiom as
    // `command.rs`'s own `termination_suffix`.
    for (kind_name, open) in [
        ("Lean.Parser.Syntax.sepBy", "sepBy("),
        ("Lean.Parser.Syntax.sepBy1", "sepBy1("),
    ] {
        b.leading2(
            "stx",
            kind_name,
            MAX_PREC,
            seq([
                sym(open),
                many1(cat("stx", 0)),
                sym(","),
                Prim::StrLit,
                opt(seq([sym(","), many1(cat("stx", 0))])),
                opt(seq([
                    sym(","),
                    Prim::NonReservedSymbol("allowTrailingSep".into()),
                ])),
                sym(")"),
            ]),
        );
    }

    // Syntax.atom := strLit — self-wraps (confirmed: `"wob"` dumps as
    // `Lean.Parser.Syntax.atom{str{"wob"}}`, NOT a bare unwrapped `str`
    // leaf like `notationItem`'s inline strLit alternative
    // — `command_notation.rs`'s `notationItem` is a plain `Parser`
    // alternation, never itself category-registered, so it never
    // self-wraps; `Syntax.atom` IS a real `leading_parser` here).
    b.leading2("stx", "Lean.Parser.Syntax.atom", MAX_PREC, Prim::StrLit);

    // Syntax.nonReserved := "&" >> strLit` — e.g. `&"weird"`.
    b.leading2(
        "stx",
        "Lean.Parser.Syntax.nonReserved",
        MAX_PREC,
        seq([sym("&"), Prim::StrLit]),
    );

    // Init/Notation.lean:171,192,224 quantifier-suffix trio (module doc
    // above): TRAILING `stx`-category entries, `lhs_prec = MAX_PREC`
    // (`stx:max`), own registered `prec = ARG_PREC` (`:arg`). Kind
    // names transcribed VERBATIM from the dump, guillemets included
    // where Lean's own `Name.toString` needs them (`+`/`,*` aren't
    // legal identifier characters; `?` is).
    b.trailing2("stx", "«stx_+»", ARG_PREC, MAX_PREC, sym("+"));
    b.trailing2("stx", "stx_?", ARG_PREC, MAX_PREC, sym("?"));
    b.trailing2("stx", "«stx_,*»", ARG_PREC, MAX_PREC, sym(",*"));
}

/// `Lean.Parser.Command.catBehaviorBoth := nonReservedSymbol "both"`,
/// `.catBehaviorSymbol := nonReservedSymbol "symbol"` (each a bare,
/// self-wrapping `leading_parser`) — `catBehavior := optional (" (" >>
/// nonReservedSymbol "behavior" >> " := " >> (catBehaviorBoth <|>
/// catBehaviorSymbol) >> ")")`. Confirmed against a fresh dump of
/// `declare_syntax_cat gadget (behavior := symbol)` (module doc above);
/// `catBehaviorBoth`'s own shape wasn't separately committed (`(behavior
/// := both)` probed only in scratch, byte-identical modulo the matched
/// keyword — same "one alternative pins the shared shape" idiom
/// `command_notation.rs`'s `mixfixKind` module doc already uses for its
/// five fixity keywords).
fn cat_behavior(b: &mut SnapshotBuilder) -> Prim {
    let both_k = b.kind("Lean.Parser.Command.catBehaviorBoth");
    let symbol_k = b.kind("Lean.Parser.Command.catBehaviorSymbol");
    opt(seq([
        sym("("),
        Prim::NonReservedSymbol("behavior".into()),
        sym(":="),
        or_else([
            nd(both_k, Prim::NonReservedSymbol("both".into())),
            nd(symbol_k, Prim::NonReservedSymbol("symbol".into())),
        ]),
        sym(")"),
    ]))
}

/// Command-side `macroArg := leading_parser optional (atomic (ident >>
/// checkNoWsBefore ":")) >> syntaxParser argPrec` — see module doc for
/// why this is NOT the same node as `term_pragma.rs`'s term-side
/// `macro_arg` (that one has no kind at all; this one self-wraps).
/// `atomic`'s backtrack scope doesn't affect the success-path shape
/// (same reasoning as `command_notation.rs`'s own optPrecedence note).
/// Omits the oracle's zero-width `checkNoWsBefore` between `ident` and
/// `":"`: this port over-accepts a stray space there (`x : term` where
/// the oracle requires `x:term`), nothing more — no other shape or
/// success/failure divergence.
fn macro_arg(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Command.macroArg");
    nd(
        k,
        seq([
            opt(atomic(seq([Prim::Ident, sym(":")]))),
            cat("stx", ARG_PREC),
        ]),
    )
}

/// `macroRhs := leading_parser withPosition termParser` — self-wraps
/// (own node); `withPosition` omitted (module doc).
fn macro_rhs(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Command.macroRhs");
    nd(k, cat("term", 0))
}
/// `macroTail := leading_parser atomic (" : " >> ident) >> darrow >>
/// macroRhs` — `darrow` is the bare `"=>"` atom (confirmed by dump,
/// same as every other `=>`-using production in this crate).
fn macro_tail(b: &mut SnapshotBuilder) -> Prim {
    let rhs = macro_rhs(b);
    let k = b.kind("Lean.Parser.Command.macroTail");
    nd(k, seq([sym(":"), Prim::Ident, sym("=>"), rhs]))
}

/// `Lean/Parser/Syntax.lean:126` (M3b3 Task 10) defines `elabTail` as
/// `atomic (" : " ident (optional (" <= " ident)))` sequenced with
/// `darrow` then `withPosition termParser`. UNLIKE `macroTail`, the RHS
/// term is NOT wrapped in a named `macroRhs`-style node — dump-confirmed
/// (`StxElab.stx.jsonl`): `elabTail`'s node-only children are just
/// `[null(<= wrapper), <term node>]`, no intermediate node at all — and
/// there's an extra optional `<= expectedType` binder slot before the
/// `=>`. That slot is ignored by `derive_elab_cmd` (it never reads past
/// the tail's own leading `ident`) and, structurally, can never shadow
/// that read either: it's nested one level inside its own `null`
/// wrapper, invisible to a direct (non-descending) token scan.
fn elab_tail(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Command.elabTail");
    nd(
        k,
        seq([
            sym(":"),
            Prim::Ident,
            opt(seq([sym("<="), Prim::Ident])),
            sym("=>"),
            cat("term", 0),
        ]),
    )
}

/// `optKind := optional (" (" >> nonReservedSymbol "kind" >> " := " >>
/// ident >> ")")` — `macro_rules`/`elab_rules`'s own optional kind-name
/// override (only `macro_rules` is ported; `elab_rules` isn't a
/// surface-table row this task owns — shape-only even in real Lean,
/// `derive_surface`'s own `"elab_rules"` arm). The populated shape
/// (`(kind := myKind)`, module doc's `probe5` citation above) is
/// dump-confirmed via that scratch probe only — no committed fixture
/// exercises it; only the empty case round-trips through one.
fn opt_kind_clause() -> Prim {
    opt(seq([
        sym("("),
        Prim::NonReservedSymbol("kind".into()),
        sym(":="),
        Prim::Ident,
        sym(")"),
    ]))
}

pub(super) fn register(b: &mut SnapshotBuilder) {
    register_stx_items(b);

    // syntaxCat := leading_parser optional docComment >>
    // "declare_syntax_cat " >> ident >> catBehavior.
    let doc = doc_comment(b);
    let behavior = cat_behavior(b);
    b.leading2(
        "command",
        "Lean.Parser.Command.syntaxCat",
        MAX_PREC,
        seq([opt(doc), sym("declare_syntax_cat"), Prim::Ident, behavior]),
    );

    // «syntax» := leading_parser optional docComment >> optional
    // Term.«attributes» >> Term.attrKind >> "syntax " >> optPrecedence
    // >> optNamedName >> optNamedPrio >> many1 (ppSpace >> syntaxParser
    // argPrec) >> " : " >> ident.
    let doc = doc_comment(b);
    let attrs = attributes(b);
    let ak = attr_kind(b);
    let prec = opt(precedence(b));
    let nn = opt(named_name(b));
    let np = opt(named_prio(b));
    b.leading2(
        "command",
        "Lean.Parser.Command.syntax",
        MAX_PREC,
        seq([
            opt(doc),
            opt(attrs),
            ak,
            sym("syntax"),
            prec,
            nn,
            np,
            many1(cat("stx", ARG_PREC)),
            sym(":"),
            Prim::Ident,
        ]),
    );

    // syntaxAbbrev := leading_parser optional docComment >> optional
    // visibility >> "syntax " >> ident >> " := " >> many1 syntaxParser.
    // `visibility` hoisted to `command.rs` (shared with `decl_
    // modifiers`), NOT `Term.attrKind` — a real divergence from
    // `syntax`/`macro_rules`/`macro`'s own attrKind-based prefix,
    // confirmed against the fresh dump (module doc above).
    let doc = doc_comment(b);
    let vis = visibility(b);
    b.leading2(
        "command",
        "Lean.Parser.Command.syntaxAbbrev",
        MAX_PREC,
        seq([
            opt(doc),
            opt(vis),
            sym("syntax"),
            Prim::Ident,
            sym(":="),
            many1(cat("stx", 0)),
        ]),
    );

    // «macro_rules» := suppressInsideQuot <| leading_parser optional
    // docComment >> optional Term.«attributes» >> Term.attrKind >>
    // "macro_rules" >> optKind >> Term.matchAlts. `Term.matchAlts`/
    // `Term.matchAlt` (`term.rs`, already ported for `match`) reused
    // UNCHANGED with `rhs = cat("term", 0)` — module doc explains why
    // no `macro_rules`-specific rhs variant is needed.
    let doc = doc_comment(b);
    let attrs = attributes(b);
    let ak = attr_kind(b);
    let alts = match_alts(b, cat("term", 0));
    b.leading2(
        "command",
        "Lean.Parser.Command.macro_rules",
        MAX_PREC,
        seq([
            opt(doc),
            opt(attrs),
            ak,
            sym("macro_rules"),
            opt_kind_clause(),
            alts,
        ]),
    );

    // «macro» := leading_parser suppressInsideQuot <| optional docComment
    // >> optional Term.«attributes» >> Term.attrKind >> "macro" >>
    // optPrecedence >> optNamedName >> optNamedPrio >> many1 (ppSpace >>
    // macroArg) >> macroTail.
    let doc = doc_comment(b);
    let attrs = attributes(b);
    let ak = attr_kind(b);
    let prec = opt(precedence(b));
    let nn = opt(named_name(b));
    let np = opt(named_prio(b));
    let arg = macro_arg(b);
    let tail = macro_tail(b);
    b.leading2(
        "command",
        "Lean.Parser.Command.macro",
        MAX_PREC,
        seq([
            opt(doc),
            opt(attrs),
            ak,
            sym("macro"),
            prec,
            nn,
            np,
            many1(arg),
            tail,
        ]),
    );

    // «elab» := leading_parser suppressInsideQuot <| optional docComment
    // >> optional Term.«attributes» >> Term.attrKind >> "elab" >>
    // optPrecedence >> optNamedName >> optNamedPrio >> many1 (ppSpace >>
    // elabArg) >> elabTail (`Lean/Parser/Syntax.lean:127-129`, M3b3 Task
    // 10). `elabArg := macroArg` (a plain alias — reuses `macro_arg`'s
    // own node kind, never registering a distinct "elabArg" one,
    // dump-confirmed) — mirrors `macro`'s own registration immediately
    // above byte-for-byte except for the tail combinator.
    let doc = doc_comment(b);
    let attrs = attributes(b);
    let ak = attr_kind(b);
    let prec = opt(precedence(b));
    let nn = opt(named_name(b));
    let np = opt(named_prio(b));
    let arg = macro_arg(b);
    let tail = elab_tail(b);
    b.leading2(
        "command",
        "Lean.Parser.Command.elab",
        MAX_PREC,
        seq([
            opt(doc),
            opt(attrs),
            ak,
            sym("elab"),
            prec,
            nn,
            np,
            many1(arg),
            tail,
        ]),
    );

    // binderPredicate := leading_parser optional docComment >> optional
    // Term.attributes >> optional Term.attrKind >> "binder_predicate" >>
    // optNamedName >> optNamedPrio >> ppSpace >> ident >> many (ppSpace
    // >> macroArg) >> " => " >> termParser (`Lean/Parser/Syntax.lean:
    // 137-139`, M3b3 Task 10). The DOUBLE-wrapped attrKind (`opt(ak)`,
    // not the bare `ak` every other attrKind-anchored command above
    // registers) is a genuine divergence, dump-confirmed
    // (`StxElab.stx.jsonl`) — `derive_binder_predicate`'s own doc
    // comment has the full citation. No `optPrecedence` slot at all
    // (unlike `syntax`/`macro`/`elab`). The bound `ident` (`x` in
    // `Init/BinderPredicates.lean`'s own declarations) is a bare token,
    // read directly via `Prim::Ident`, same as `macroTail`'s target
    // category ident.
    let doc = doc_comment(b);
    let attrs = attributes(b);
    let ak = opt(attr_kind(b));
    let nn = opt(named_name(b));
    let np = opt(named_prio(b));
    let arg = macro_arg(b);
    b.leading2(
        "command",
        "Lean.Parser.Command.binderPredicate",
        MAX_PREC,
        seq([
            opt(doc),
            opt(attrs),
            ak,
            sym("binder_predicate"),
            nn,
            np,
            Prim::Ident,
            many(arg),
            sym("=>"),
            cat("term", 0),
        ]),
    );
}
