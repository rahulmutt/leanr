//! Notation kind-name mangler (M3b1 Task 3 — spec §Surface→parser
//! derivation, "the sharpest correctness risk"). `mangle_kind` is a
//! PURE port of the rule Lean's notation elaborator uses to name the
//! syntax node kind it auto-generates for a `notation`/`infixl`/
//! `infixr`/`infix`/`prefix`/`postfix` declaration — never invented,
//! read off a real oracle dump (below) and cross-checked against the
//! pinned toolchain's own source.
//!
//! ## Oracle dump (Task 3 Step 1)
//!
//! The committed `dump_syntax.lean` runner is parse-only (no
//! elaboration — see its own header comment), so it can't observe a
//! notation's GENERATED kind: registering it requires actually running
//! the `notation`/`mixfix` command elaborator, which extends the
//! environment's parser tables, before parsing a USE of the notation.
//! A scratch investigation script (`_scratch_task3/dump_elab.lean`,
//! deleted before commit — not part of the repo's grammar or fixture
//! set) drove `Lean.Elab.Frontend.IO.processCommands` instead of bare
//! `Parser.parseCommand`, so each command actually elaborates (updating
//! the env) before the next one is parsed. Two calls were needed first:
//! `Lean.enableInitializersExecution` before `Parser.parseHeader`/
//! `processHeader` (otherwise `importModules (loadExts := true)`
//! throws and the header silently resolves to an empty environment —
//! caught by printing `processHeader`'s returned `MessageLog`, which
//! the committed dumper never prints because it doesn't need to), and
//! dropping the `prelude` directive the M3a-era probes used (`prelude`
//! suppresses the implicit `import Init`, so nothing above the literal
//! builtin parser tables resolves during elaboration — again, harmless
//! for a parse-only dump, fatal for one that elaborates).
//!
//! Probe 1 — `crates/leanr_syntax/../_scratch_task3/probe_infix.lean`:
//! ```text
//! infixl:65 " ⊗ " => Sum
//! example := a ⊗ b
//! ```
//! dumped `k` for the `example`'s value (3rd top-level JSONL line,
//! `declValSimple`'s 2nd child):
//! ```text
//! {"c":[{"i":"a","s":[36,37]},{"a":"⊗","s":[38,41]},{"i":"b","s":[42,43]}],"k":"«term_⊗_»"}
//! ```
//! (`⊗` chosen over the brief's illustrative `⊕` because Lean's own
//! `Init.Core` already declares `infixr:30 " ⊕ " => Sum` — reusing `⊕`
//! produces a `choice` node between the pre-existing declaration and a
//! `_1`-suffixed fresh one, an unrelated collision-avoidance mechanism;
//! see "Deliberately out of scope" below. `⊗`/`~` are collision-free at
//! top level in this pin, confirmed by grep over `Init/`.)
//!
//! Probe 2 — `probe_prefix.lean`:
//! ```text
//! prefix:100 "~" => Not
//! example := ~a
//! ```
//! dumped `k`:
//! ```text
//! {"c":[{"a":"~","s":[33,34]},{"i":"a","s":[34,35]}],"k":"«term~_»"}
//! ```
//! — both byte-exact matches to the brief's illustrative
//! `«term_⊕_»`/`«term~_»` shapes (guillemets are U+00AB/U+00BB,
//! confirmed by codepoint inspection, not eyeballing).
//!
//! Probe 3 — `probe_alpha.lean` (the rule is MORE than "concat trimmed
//! symbols and underscores in guillemets" — this probe is why):
//! ```text
//! notation "myOp" x:100 => Not x
//! example := myOp a
//! ```
//! dumped `k`:
//! ```text
//! {"c":[{"a":"myOp","s":[42,46]},{"i":"a","s":[47,48]}],"k":"termMyOp_"}
//! ```
//! Two things this shows that probes 1/2 don't exercise: (a) no
//! guillemets — `termMyOp_` is already a valid plain identifier; (b)
//! the symbol atom's first character is capitalized (`myOp` →
//! `MyOp`), even though nothing was quoted with a leading placeholder.
//!
//! ## The rule, ported from source (pin v4.32.0-rc1)
//!
//! Reading `Lean/Elab/Syntax.lean`'s `mkNameFromParserSyntax` (the
//! function that names a fresh `syntax`/`notation` declaration when the
//! user didn't give one explicitly via `(name := ..)`) against the
//! three probes above:
//!
//! - Each atom contributes, in order, onto an accumulator seeded with
//!   `category`:
//!   - `Placeholder` (Lean: a `Syntax.Syntax.cat` child, i.e. a bound
//!     `term`/etc. argument) → literal `_`.
//!   - `Symbol(s)` (Lean: a quoted string-literal atom) → `s` with
//!     Lean-whitespace (`Char.isWhitespace` — ASCII-only `' '`/`'\t'`/
//!     `'\r'`/`'\n'`, per `Init/Data/Char/Basic.lean:97`; NOT Rust's
//!     `is_ascii_whitespace`, which also matches `\x0B`/`\x0C`) trimmed
//!     from both ends (`String.trimAscii`), any *interior* such
//!     whitespace turned into `_`, then `String.capitalize`d — which is
//!     `Char.toUpper` on just the first character, and `Char.toUpper`
//!     (`Init/Data/Char/Basic.lean:173`) only affects ASCII `a`-`z`, so
//!     a bare-punctuation atom like `⊗`/`~` is unaffected while a
//!     keyword atom like `"myOp"` becomes `"MyOp"`.
//! - The category is concatenated directly (`appendCatName`: no `.`
//!   separator between `category` and the atoms' contributions).
//! - Finally, the whole string becomes the printed form of a
//!   single-component `Lean.Name` (`stxNodeKind := currNamespace ++
//!   name`, then `kind.toString`): `Name.escapePart`/`needsNoEscape`
//!   (`Init/Data/ToString/Name.lean`) wraps it in guillemets (`«`/`»`,
//!   U+00AB/U+00BB) UNLESS it already reads as a plain identifier —
//!   first char passes `isIdFirst`, every other char passes `isIdRest`
//!   (`Init/Meta/Defs.lean:120,133` — the SAME character classes
//!   `crate::lex::is_id_first`/`is_id_rest` already port for lexing, so
//!   reused here rather than redefined).
//!
//! ## Deliberately out of scope
//!
//! Real Lean also de-duplicates against EXISTING declarations
//! (`mkUnusedBaseName`, appending `_1`/`_2`/… on collision — visible in
//! probe 1's raw dump before `⊗` was substituted for `⊕`). That needs
//! environment/scope state this function doesn't have and isn't part
//! of its contract (`mangle_kind(category, atoms) -> String`, no
//! "already-used names" input); it's a concern for whatever registers
//! the mangled kind into an `Overlay`, not for this pure mangler.
//! Likewise `currNamespace ++ name`: this function returns the LOCAL
//! (category-scoped) name only, not a namespace-qualified one —
//! matching the brief's category-only signature.

use crate::kind::{KindInterner, KIND_ERROR, KIND_IDENT, KIND_MISSING};
use crate::lex::{is_id_first, is_id_rest};
use crate::tree::SyntaxNode;

use super::{LeadingIdentBehavior, Prim, LEAD_PREC, MAX_PREC};

/// One atom of a notation's surface syntax, in declaration order.
/// `Symbol` carries the *raw* (untrimmed) source text of a quoted
/// atom, e.g. `" ⊗ "` (with its surrounding notation-spacing) or
/// `"myOp"`/`"~"` (already bare) — `mangle_kind` does the trimming.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NotationAtom {
    Symbol(String),
    Placeholder,
}

/// Reproduces Lean's generated notation kind name. Rule confirmed
/// against the oracle dump in Task 3 Step 1 (module doc above) — kept
/// byte-exact (oracle equality depends on it). Pure: never panics on
/// any input, including empty `atoms`/`category` or a `Symbol` whose
/// trimmed contents are empty.
pub fn mangle_kind(category: &str, atoms: &[NotationAtom]) -> String {
    escape_name_component(&mangle_kind_unescaped(category, atoms))
}

/// The un-escaped local (category-scoped) name — `mangle_kind` minus
/// the final guillemet-wrapping step. Pulled out (M3b1 Task 8) so
/// `mangle_private_kind` below can apply `escape_name_component` to
/// just this ONE `Name` component, matching how Lean's own
/// `Name.toString` escapes a MULTI-component `Name` component-by-
/// component, not as a single joined string (see `mangle_private_kind`'s
/// own doc comment for the oracle dump that shows this).
fn mangle_kind_unescaped(category: &str, atoms: &[NotationAtom]) -> String {
    let mut base = String::from(category);
    for atom in atoms {
        match atom {
            NotationAtom::Placeholder => base.push('_'),
            NotationAtom::Symbol(s) => base.push_str(&mangle_symbol_atom(s)),
        }
    }
    base
}

/// The `local notation`/`local infixl`/… kind name — DISTINCT from
/// `mangle_kind`, discovered by Task 8's oracle gate (`NotationLocal.
/// lean`), not anticipated by Task 3/4's original derivation.
///
/// ORACLE DUMP (Task 8, `dump_syntax_elab.lean` — the elaborating
/// dumper, since this is a Lean ELABORATOR behavior, `Lean/Elab/
/// Syntax.lean:432-433`'s `elabSyntax`, invisible to any parse-only
/// dump): `local notation "★" => Sum` used as `★` generates kind
/// ```text
/// "_private.0.«term★»"
/// ```
/// not the plain `mangle_kind`-shape `"«term★»"` a non-`local`
/// `notation` with the same atoms would get.
///
/// SOURCE (pin v4.32.0-rc1): `elabSyntax` only applies this when
/// `attrKind matches \`(attrKind| local)` (`Lean/Elab/Syntax.lean:432` —
/// `scoped` does NOT trigger it, matching this crate's design spec §7
/// "`local notation` in scope, `scoped` excluded"): `stxNodeKind :=
/// mkPrivateName (← getEnv) stxNodeKind`. `mkPrivateName`/
/// `mkPrivateNameCore` (`Lean/PrivateName.lean:26-30`): `Name.mkNum
/// (\`_private ++ mainModule) 0 ++ n` — a name is NEVER a single
/// string, it's Lean's own linked-list `Name` type, and `Name.toString`
/// (what `kind.toString` — this crate's whole oracle-comparison point —
/// actually calls) escapes each `.str`/`.num` COMPONENT independently
/// (`escapePart`/`needsNoEscape`, same rule `escape_name_component`
/// already ports), then joins with `.` — NOT one `escape_name_component`
/// call over the whole concatenated string. `_private` and the literal
/// `0` component are always plain (never need escaping); only the
/// LAST component (`n`, this notation's own unescaped mangled name)
/// ever needs guillemets — reproduced here as `escape_name_component`
/// applied to JUST `mangle_kind_unescaped`'s output, not the joined
/// `"_private.0.…"` string.
///
/// `mainModule` (the file's own dotted module name, e.g. what a real
/// `lean tests/fixtures/syntax/NotationLocal.lean -o …` compile derives
/// from the file's path relative to the invoking `lean`'s CWD —
/// `Lean/Util/Path.lean`'s `moduleNameOfFileName`) is DELIBERATELY
/// treated as `Name.anonymous` here, for two independent reasons: (1)
/// `parse_module`'s own public signature (`fn parse_module(src: &str,
/// snap: &GrammarSnapshot)`) never receives a file path or module name
/// — there is no input to derive one from; (2) this crate's dumper
/// (`dump_syntax_elab.lean`) ALSO never passes a `mainModule` to
/// `processHeader` (defaults `Name.anonymous`), matching every other
/// fixture in this corpus being hermetic/path-independent (renaming or
/// relocating a fixture file must not change its committed dump) — so
/// `Name.anonymous` is the oracle-CONFIRMED, stable ground truth here,
/// not an approximation of a path-dependent value this crate can't
/// compute. With `mainModule = anonymous`, `\`_private ++ mainModule`
/// collapses to plain `\`_private` (`Name.append n .anonymous = n`),
/// which is exactly the constant `"_private.0."` prefix hardcoded
/// below.
fn mangle_private_kind(category: &str, atoms: &[NotationAtom]) -> String {
    format!(
        "_private.0.{}",
        escape_name_component(&mangle_kind_unescaped(category, atoms))
    )
}

/// `Char.isWhitespace` (`Init/Data/Char/Basic.lean:97`, pin
/// v4.32.0-rc1): exactly space/tab/CR/LF — narrower than Rust's
/// `char::is_ascii_whitespace` (which also accepts `\x0B`/`\x0C`).
fn is_lean_whitespace(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\r' | '\n')
}

/// `String.trimAscii` + interior-whitespace-to-`_` + `String.capitalize`
/// (`Init/Data/String/{TakeDrop,Modify}.lean`), applied to one quoted
/// symbol atom's raw text.
///
/// `pub(super)` (M3b2b Task 8): `grammar::surface`'s own `mangle_visit`
/// (the general `syntax`-command mangler, ORACLE-PORT of
/// `mkNameFromParserSyntax`'s `visit`) needs this exact same per-atom
/// transform for a `str`-shaped node it walks — reused rather than
/// redefined, same "one pinned rule" discipline this file's own module
/// doc already states for `mangle_kind`.
pub(super) fn mangle_symbol_atom(raw: &str) -> String {
    let trimmed = raw.trim_matches(is_lean_whitespace);
    let underscored: String = trimmed
        .chars()
        .map(|c| if is_lean_whitespace(c) { '_' } else { c })
        .collect();
    capitalize_first_ascii(&underscored)
}

/// `String.capitalize` (`Init/Data/String/Modify.lean:246`): apply
/// `Char.toUpper` to just the first character. `Char.toUpper`
/// (`Init/Data/Char/Basic.lean:173`) is a no-op outside ASCII `a`-`z`.
fn capitalize_first_ascii(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => {
            let mut out = String::with_capacity(s.len());
            out.push(if c.is_ascii_lowercase() {
                c.to_ascii_uppercase()
            } else {
                c
            });
            out.push_str(chars.as_str());
            out
        }
    }
}

/// `Name.escapePart`/`needsNoEscape` (`Init/Data/ToString/Name.lean`),
/// specialized to a single-component `Name` (no `.`-separated parts —
/// `mangle_kind` never produces one) with `isToken` always false, which
/// is how `kind.toString` (this crate's oracle-dump comparison point,
/// same as the committed `dump_syntax.lean`'s `toCanon`) prints a
/// `Name`.
///
/// `pub` (same promotion already done for `trim_lean_symbol`): reused
/// by `leanr_grammar::descr` to build the ESCAPED display form of an
/// imported parser's kind `Name` component-by-component (M3b2a Task 6
/// review Finding 1), matching the oracle dump's `«term_⊕⊕_»`-style
/// guillemet-quoting instead of interning the raw joined name.
pub fn escape_name_component(s: &str) -> String {
    if needs_no_escape(s) {
        return s.to_string();
    }
    if s.contains('»') {
        // `escapePart` returns `none` here; `Name.toStringWithSep`'s
        // `maybeEscape` falls back to the unescaped string
        // (`escapePart s force |>.getD s`).
        return s.to_string();
    }
    format!("«{s}»")
}

/// `pub` alongside `escape_name_component` (same reuse rationale).
pub fn needs_no_escape(s: &str) -> bool {
    let mut chars = s.chars();
    match chars.next() {
        Some(first) => is_id_first(first) && chars.all(is_id_rest),
        None => false,
    }
}

// ============================================================
// Derivation (M3b1 Task 4): notation/mixfix command subtree ->
// `NotationSpec`. Pure — never panics on a malformed tree, returns
// `None` instead (Task 9 hardens this further for error/missing nodes
// in required slots; the `?`-propagation below already gives every
// "shape didn't match" case that seam for free).
// ============================================================

/// Derived from a parsed `notation`/`infixl`/`infixr`/`infix`/`prefix`/
/// `postfix` command (`derive`'s return value): everything Task 5 needs
/// to fold the declaration into an `Overlay` — the generated node kind,
/// whether it's a leading or trailing (Pratt) production, its
/// precedence/associativity numbers, the literal tokens it introduces,
/// and the `Prim` body to run (no outer `Node`/`TrailingNode` wrap —
/// Task 5 does that, since only it knows the final interned
/// `SyntaxKind`).
#[derive(Clone, Debug)]
pub struct NotationSpec {
    pub category: String,
    pub kind_name: String,
    /// `false` => trailing (the production has a leading placeholder
    /// that becomes the already-parsed lhs — a Pratt "trailing" entry).
    pub leading: bool,
    /// `Node`/`TrailingNode`'s own precedence level (Lean's
    /// `notation:$prec`, `ParserDescr.node`/`trailingNode`'s 2nd arg).
    pub prec: u32,
    /// `Some(p)` iff `leading == false`: the trailing entry's minimum
    /// lhs precedence (`ParserDescr.trailingNode`'s 3rd arg).
    pub lhs_prec: Option<u32>,
    /// Symbol atoms this declaration introduces as parser tokens,
    /// trimmed (Lean-whitespace, both ends — same rule `mangle_kind`
    /// applies to name-mangling, see `mangle_symbol_atom`).
    pub tokens: Vec<String>,
    /// `Prim::Seq` of `Prim::Symbol`/`Prim::Category` recursions, in
    /// declaration order, EXCLUDING the leading placeholder when
    /// `leading == false` (that lhs is the Pratt wrap, never a body
    /// child — see `Prim::TrailingNode`'s own doc comment in
    /// `grammar/mod.rs`).
    pub body: Prim,
}

/// One item of a notation/mixfix's surface syntax, in declaration
/// order — an intermediate shape this module builds either straight
/// off the `notation` command's own `notationItem`s, or synthesized
/// from a `mixfix` alternative's closed-form macro expansion (see
/// `mixfix_items`'s doc comment). `Placeholder`'s `Option<u32>` is the
/// item's own explicit `:prec` annotation, `None` when omitted —
/// deliberately NOT resolved to a default here, so the one place that
/// needs the default (`build_spec`, for the leading/lhs placeholder;
/// `Prim::Category`'s own construction, for every other placeholder)
/// applies it explicitly, matching `Lean/Elab/Syntax.lean`'s own
/// `expandOptPrecedence`'s `prec?.getD 0` (`checkLeftRec`,
/// `processParserCategory`, pin v4.32.0-rc1) at the one place it fires.
#[derive(Clone, Debug)]
enum Item {
    /// Raw (untrimmed, quote-delimiters-already-stripped) text of a
    /// quoted symbol atom — same contract as `NotationAtom::Symbol`.
    Symbol(String),
    Placeholder(Option<u32>),
}

/// M3b2b Task 7: `derive`'s generalized return type — a grammar-growing
/// command derives EITHER a new PRODUCTION to fold into an existing
/// category (`notation`/`mixfix`, exactly the old `derive`'s plain
/// `NotationSpec` result) OR a brand-new, initially-EMPTY CATEGORY
/// (`declare_syntax_cat` — Task 8 registers productions into it; until
/// then the category exists only for a category antiquot, `$x`, to
/// resolve into — see `parse.rs`'s `category()` overlay fallback).
#[derive(Clone, Debug)]
pub enum GrammarDelta {
    Production(NotationSpec),
    NewCategory {
        name: String,
        behavior: LeadingIdentBehavior,
    },
}

/// Entry point (brief's `pub fn derive_delta`, M3b2b Task 7 — supersedes
/// M3b1's plain `derive`, single call site updated in place rather than
/// kept as a wrapper, see this task's report for the `grep` that found
/// no other call sites). `None` iff `node.kind()` is not a grammar-
/// growing outer kind (`notation`/`mixfix`/`declare_syntax_cat`), OR the
/// subtree doesn't match this module's oracle-confirmed shape for that
/// kind (malformed/error-node trees — Task 9's formal remit, but every
/// navigation step below is already `?`-propagated `Option`, so it falls
/// out for free rather than needing a dedicated guard), OR (Task 9 Step
/// 3, defense in depth — see `contains_error_or_missing`'s own doc
/// comment) `node` contains an `<error>`/`<missing>` node anywhere in
/// its structural slots.
pub fn derive_delta(node: &SyntaxNode, kinds: &KindInterner) -> Option<GrammarDelta> {
    // M3b1 only ever registers into the `term` category (both
    // `mixfix`'s and `notation`'s own RHS recurse via `cat("term", 0)`
    // — command_notation.rs's `register`) — hardcoded per the task
    // brief rather than read off the tree, since neither command shape
    // this crate parses carries an explicit category annotation of its
    // own (real Lean's `notation` always targets `term` too — see
    // `elabNotation`'s `let cat := mkIdentFrom ref \`term`).
    let category = "term";
    let name = kinds.name(node.kind());
    // Task 9 Step 3: refuse to derive a delta from a subtree that isn't
    // STRUCTURALLY clean, even though it reached this call via the
    // command loop's own clean `Ok(())` arm (`parse.rs`'s `run_module`,
    // M3b1 Task 7) — see `contains_error_or_missing`'s own doc comment
    // for why this is currently unreachable-by-construction on this
    // crate's grammar, and why the guard is kept anyway. Applies
    // uniformly to every kind dispatched below — no slot in any of
    // their oracle shapes is allowed to legitimately contain one.
    if contains_error_or_missing(node) {
        return None;
    }
    match name {
        "Lean.Parser.Command.mixfix" => {
            derive_mixfix(node, kinds, category).map(GrammarDelta::Production)
        }
        "Lean.Parser.Command.notation" => {
            derive_notation(node, kinds, category).map(GrammarDelta::Production)
        }
        "Lean.Parser.Command.syntaxCat" => derive_syntax_cat(node, kinds),
        // M3b2b Task 8: the general `syntax`-command surface (`syntax`/
        // `syntaxAbbrev`/`macro`/the imported `elab`-family) — one
        // dispatch entry point for `run_module`, per this task's brief.
        _ => super::surface::derive_surface(node, kinds),
    }
}

/// `declare_syntax_cat`'s oracle shape (`command_syntax.rs`'s module
/// doc, Task 6's oracle dump): `Lean.Parser.Command.syntaxCat{
/// null(doc), "declare_syntax_cat"(atom), ident(bare token),
/// null(catBehavior) }`. Both `sym("declare_syntax_cat")` and
/// `Prim::Ident` are bare TOKENS (no node wrap — the same token/node
/// split `derive_notation`'s own doc comment already establishes for
/// `notation`'s bare `"notation"` keyword and `identPrec`'s bare
/// leading `ident`), so `node.children()` (nodes only) sees exactly 2
/// node children: the `null(doc)` wrapper (unused here — doc comments
/// are out of this task's scope) and the `null(catBehavior)` wrapper.
fn derive_syntax_cat(node: &SyntaxNode, kinds: &KindInterner) -> Option<GrammarDelta> {
    let name = first_ident_token_text(node)?;
    let children: Vec<SyntaxNode> = node.children().collect();
    let behavior_wrapper = children.get(1)?;
    let behavior = match behavior_wrapper.children().next() {
        Some(inner) => match kinds.name(inner.kind()) {
            "Lean.Parser.Command.catBehaviorBoth" => LeadingIdentBehavior::Both,
            "Lean.Parser.Command.catBehaviorSymbol" => LeadingIdentBehavior::Symbol,
            // Malformed/unexpected behavior shape (Task 9's formal
            // remit; never panic here either way) — bail out with
            // `None`.
            _ => return None,
        },
        None => LeadingIdentBehavior::Default,
    };
    Some(GrammarDelta::NewCategory { name, behavior })
}

/// First TOKEN child of `node` whose token KIND is `KIND_IDENT` —
/// unlike `first_token_text` (which returns a node's ONE token,
/// unconditionally the first), `declare_syntax_cat`'s outer node has
/// TWO direct token children (the bare `"declare_syntax_cat"` keyword
/// atom, then the category name ident) since neither is wrapped in its
/// own node — this picks the ident out by token KIND rather than
/// position, so it's robust regardless of what (if anything) sits
/// ahead of it.
///
/// `pub(super)` (M3b2b Task 8): `grammar::surface` reuses this to pull
/// the fn-name/category-name ident off `Syntax.cat`/`.unary`/`.binary`
/// nodes, which have the identical "bare ident token, not the first
/// CHILD element overall" shape.
pub(super) fn first_ident_token_text(node: &SyntaxNode) -> Option<String> {
    node.children_with_tokens().find_map(|el| {
        let t = el.into_token()?;
        (t.kind() == KIND_IDENT).then(|| t.text().to_string())
    })
}

/// Task 9 Step 3 (defense in depth, task-9-brief's Step 3): `true` iff
/// `node` or anything nested inside it — node OR leaf token, any
/// depth — is an `<error>` node (`KIND_ERROR`, the node
/// `Ps::recover_command` wraps its swept tokens in) or a `<missing>`
/// leaf (`KIND_MISSING`, this crate's `Syntax.missing`, emitted only by
/// `Prim::EmitMissing`/`Event::Missing`).
///
/// **Why the whole subtree, not just the four slots the brief names as
/// examples** (the fixity keyword, the symbol atom, `=>`, the RHS
/// term): scanning everything is a strict SUPERSET of "scan the
/// required slots" — it can only reject MORE trees, never fewer — and
/// it's safe to be that broad here specifically because there is no
/// slot in `mixfix`/`notation`'s own oracle shape that is allowed to
/// legitimately contain `<error>`/`<missing>`: every OPTIONAL slot
/// (`namedName`, `namedPrio`, `notation`'s own top-level `precedence`,
/// `identPrec`'s inner `precedence`) is `opt(..)`-wrapped, and a
/// genuinely-absent optional emits a plain, EMPTY `null` node
/// (`Prim::Optional`'s non-consuming-failure arm, `parse.rs`) — never
/// `<missing>` — so this scan cannot false-reject a valid fixture whose
/// optional slots are simply unused (confirmed by the full regression
/// run below finding zero valid-fixture regressions).
///
/// **Why this is provably unreachable today, and why the guard is
/// still worth keeping** (Task 9 brief's own instruction — "a command
/// can parse as a clean `Ok` while still containing an error/missing
/// node in a structural slot"): reading `parse.rs`'s `Ps::run` shows
/// `<error>` nodes are emitted in exactly ONE place in this whole
/// crate — `Ps::recover_command`, called only by `run_module`'s own
/// top-level command loop, never from inside a `Prim::Seq`/`Node`
/// body — and `<missing>` leaves are emitted in exactly ONE place —
/// `Prim::EmitMissing`, used only by `Prim::UnknownTacticIdent`
/// (`Tactic.«unknown»`, unrelated to `notation`/`mixfix`). Neither
/// `command_notation.rs`'s `mixfix`/`notation` productions, nor
/// anything a `cat("term", 0)` RHS recursion can reach, ever calls
/// either. And `Prim::Seq`/`Prim::OrElse`/`Prim::Optional` have NO
/// "insert `<missing>`, recover, and keep going" mode of their own — a
/// CONSUMING failure partway through a `Seq` (e.g. `sym("=>")` failing
/// because the RHS was omitted) propagates as a hard `Err` all the way
/// out to `run_module`'s loop, which then takes the `Err(_)`
/// arm — `restore(&sp)` + `recover_command()` — NOT the clean `Ok(())`
/// arm this function is only ever called from. So today, every subtree
/// this function receives that reached the `Ok(())` arm is, by
/// construction, already 100% free of `<error>`/`<missing>` — this
/// scan is a no-op on every currently-reachable input (confirmed: the
/// full regression suite below is unchanged after adding it). It stays
/// anyway as defense-in-depth against a FUTURE change this task's own
/// brief anticipates: a future per-slot recovery mode (mirroring real
/// Lean's own `errorAtSavedPos`/partial-node recovery, `Basic.lean`)
/// that lets some OTHER production reach a clean-looking `Ok(())` with
/// an `<error>`/`<missing>` spliced into one of ITS slots, which — if
/// this crate's `notation`/`mixfix` productions ever grew one too —
/// would otherwise let a half-built parser register silently.
fn contains_error_or_missing(node: &SyntaxNode) -> bool {
    if node.kind() == KIND_ERROR {
        return true;
    }
    node.children_with_tokens().any(|el| match el {
        rowan::NodeOrToken::Node(n) => contains_error_or_missing(&n),
        rowan::NodeOrToken::Token(t) => t.kind() == KIND_MISSING,
    })
}

/// `mixfix`'s oracle shape (command_notation.rs module doc, oracle dump
/// Step 1): `[null(doc), null(attrs), attrKind, mixfixKind, precedence,
/// null(namedName), null(namedPrio), str, "=>", term]`. Anchored off
/// `attrKind`'s own unique kind name (rather than a bare numeric index
/// from the root) so a doc-comment slot actually being populated
/// (still a `null`-kind NODE either way — `Optional` always emits its
/// wrapper) can't shift anything: the 3-child `notation_prefix` always
/// contributes exactly 3 node children regardless of what's inside
/// them.
fn derive_mixfix(node: &SyntaxNode, kinds: &KindInterner, category: &str) -> Option<NotationSpec> {
    let children: Vec<SyntaxNode> = node.children().collect();
    let attr_kind_pos = children
        .iter()
        .position(|c| kinds.name(c.kind()) == "Lean.Parser.Term.attrKind")?;
    let is_local = is_local_attr_kind(&children[attr_kind_pos], kinds);
    let mixfix_kind_node = children.get(attr_kind_pos + 1)?;
    let fixity = kinds.name(mixfix_kind_node.kind());
    let precedence_node = children.get(attr_kind_pos + 2)?;
    let p = read_prec_num(precedence_node, kinds)?;
    let str_node = children.get(attr_kind_pos + 5)?;
    if kinds.name(str_node.kind()) != "str" {
        return None;
    }
    let op = strip_quotes(&first_token_text(str_node)?).to_string();

    // ORACLE-PORT `Lean/Elab/Mixfix.lean`'s `expandMixfix` (pin
    // v4.32.0-rc1, lines 16-32 — read directly off the pinned
    // toolchain's own source, not inferred): each of the five
    // `mixfixKind` alternatives is a `macro_rules` arm that rewrites
    // straight to a `notation:$prec ...` with EXPLICIT `:prec`
    // annotations on every placeholder, closed-form in `p` (no
    // defaulting ever applies here, unlike a hand-written `notation`).
    // Reproduced here as the exact `Item` list that `notation:$prec`
    // arm would itself carry, then run through the SAME `build_spec`
    // a real `notation` uses — `infixl`'s own arm is literally
    // `notation:$prec lhs:$prec $op rhs:$prec1 => $f lhs rhs` (`prec1
    // := prec + 1`), etc.
    let items = match fixity {
        "Lean.Parser.Command.infixl" => vec![
            Item::Placeholder(Some(p)),
            Item::Symbol(op),
            Item::Placeholder(Some(p + 1)),
        ],
        "Lean.Parser.Command.infix" => vec![
            Item::Placeholder(Some(p + 1)),
            Item::Symbol(op),
            Item::Placeholder(Some(p + 1)),
        ],
        "Lean.Parser.Command.infixr" => vec![
            Item::Placeholder(Some(p + 1)),
            Item::Symbol(op),
            Item::Placeholder(Some(p)),
        ],
        "Lean.Parser.Command.prefix" => vec![Item::Symbol(op), Item::Placeholder(Some(p))],
        "Lean.Parser.Command.postfix" => vec![Item::Placeholder(Some(p)), Item::Symbol(op)],
        _ => return None,
    };
    // `mixfix` always supplies `:$prec` explicitly on the OUTER
    // `notation` too (`notation:$prec ...` — every `expandMixfix` arm
    // above), so unlike a hand-written `notation`, there is no
    // atom-like-defaulting case to consider here: the outer prec is
    // always exactly `p`.
    build_spec(category, items, p, is_local)
}

/// `notation`'s oracle shape (command_notation.rs module doc, oracle
/// dump Step 1): `[null(doc), null(attrs), attrKind, "notation"(atom,
/// not a node), null(precedence?), null(namedName), null(namedPrio),
/// null(many notationItem), "=>", term]`. Anchored off `attrKind` the
/// same way `derive_mixfix` is (the bare `"notation"` keyword atom is
/// a TOKEN, invisible to `SyntaxNode::children()`, so it doesn't shift
/// the node-only positions either).
fn derive_notation(
    node: &SyntaxNode,
    kinds: &KindInterner,
    category: &str,
) -> Option<NotationSpec> {
    let children: Vec<SyntaxNode> = node.children().collect();
    let attr_kind_pos = children
        .iter()
        .position(|c| kinds.name(c.kind()) == "Lean.Parser.Term.attrKind")?;
    let is_local = is_local_attr_kind(&children[attr_kind_pos], kinds);
    let prec_wrapper = children.get(attr_kind_pos + 1)?;
    let explicit_prec = find_child(prec_wrapper, "Lean.Parser.precedence", kinds)
        .and_then(|pn| read_prec_num(&pn, kinds));
    let items_wrapper = children.get(attr_kind_pos + 4)?;

    let mut items = Vec::new();
    for item_node in items_wrapper.children() {
        match kinds.name(item_node.kind()) {
            "str" => {
                let raw = strip_quotes(&first_token_text(&item_node)?).to_string();
                items.push(Item::Symbol(raw));
            }
            "Lean.Parser.Command.identPrec" => {
                // `identPrec := ident >> optional precedence` — the
                // leading `ident` is a bare TOKEN (skipped by
                // `children()`), so the ONE node child left is the
                // `optional precedence`'s own `null` wrapper.
                let prec_wrapper = item_node.children().next()?;
                let prec = find_child(&prec_wrapper, "Lean.Parser.precedence", kinds)
                    .and_then(|pn| read_prec_num(&pn, kinds));
                items.push(Item::Placeholder(prec));
            }
            // Malformed/unexpected item shape (Task 9's formal remit;
            // never panic here either way) — bail out with `None`.
            _ => return None,
        }
    }
    if items.is_empty() {
        return None;
    }

    // ORACLE-PORT `Lean/Elab/Syntax.lean`'s `elabSyntax` (pin
    // v4.32.0-rc1, lines 413-417): "If the user did not provide an
    // explicit precedence, we assign `maxPrec` to atom-like syntax and
    // `leadPrec` otherwise" — `isAtomLikeSyntax` (lines 367-376) checks
    // the FIRST and LAST item are both literal `Syntax.atom`s (a bare
    // `notation "foo" => ..` is atom-like; anything with a placeholder
    // at either end is not, since `Syntax.cat` never satisfies `kind
    // == Syntax.atom`).
    let atom_like = matches!(items.first(), Some(Item::Symbol(_)))
        && matches!(items.last(), Some(Item::Symbol(_)));
    let outer_prec = explicit_prec.unwrap_or(if atom_like { MAX_PREC } else { LEAD_PREC });
    build_spec(category, items, outer_prec, is_local)
}

/// Whether `attr_kind_node` (a `Lean.Parser.Term.attrKind` node —
/// `nd(k, opt(scoped_or_local))`, `attr.rs`'s `attr_kind`) carries the
/// `local` modifier specifically (not `scoped`, not absent) — the
/// exact condition `Lean/Elab/Syntax.lean:432`'s `elabSyntax` gates
/// `mkPrivateName` on (`mangle_private_kind`'s own doc comment has the
/// oracle dump + source citation). `attrKind`'s single child is the
/// `optional`'s own `null` wrapper: 0 children when the modifier is
/// absent, 1 child (`Lean.Parser.Term.scoped` or `Lean.Parser.Term.
/// local`) when present.
fn is_local_attr_kind(attr_kind_node: &SyntaxNode, kinds: &KindInterner) -> bool {
    attr_kind_node
        .children()
        .next()
        .and_then(|opt_wrapper| opt_wrapper.children().next())
        .is_some_and(|inner| kinds.name(inner.kind()) == "Lean.Parser.Term.local")
}

/// Shared tail end of both `derive_mixfix`/`derive_notation`: turn an
/// ordered `Item` list + the outer node's own precedence into a
/// `NotationSpec`. ORACLE-PORT `Lean/Elab/Syntax.lean`'s `checkLeftRec`
/// (pin v4.32.0-rc1, lines 75-87): the FIRST item, and ONLY the first,
/// is checked for being a same-category placeholder — if so, this
/// production is a Pratt "trailing" entry (`markAsTrailingParser`, lhs
/// precedence = that placeholder's own `:prec` or `0` if omitted,
/// `expandOptPrecedence`'s `getD 0`), and the placeholder itself is
/// STRIPPED from the body (`processSeq`: `args.eraseIdxIfInBounds 0`)
/// — it becomes the already-parsed lhs a `TrailingNode` wraps
/// automatically (`Prim::TrailingNode`'s own doc comment), never a
/// body child. Every other placeholder (first-when-leading, or any
/// interior/trailing one) becomes an ordinary `Prim::Category`
/// recursion at its own `:prec` (defaulting to `0` the same way,
/// `processParserCategory`'s identical `prec?.getD 0`).
fn build_spec(category: &str, items: Vec<Item>, prec: u32, is_local: bool) -> Option<NotationSpec> {
    if items.is_empty() {
        return None;
    }
    let atoms: Vec<NotationAtom> = items
        .iter()
        .map(|it| match it {
            Item::Symbol(s) => NotationAtom::Symbol(s.clone()),
            Item::Placeholder(_) => NotationAtom::Placeholder,
        })
        .collect();
    // M3b1 Task 8 (oracle-forced fix, `NotationLocal.lean`): `local
    // notation`/`local infixl`/… gets a DIFFERENT generated kind name
    // than the same declaration without `local` — see
    // `mangle_private_kind`'s own doc comment for the oracle dump and
    // source citation.
    let kind_name = if is_local {
        mangle_private_kind(category, &atoms)
    } else {
        mangle_kind(category, &atoms)
    };
    let tokens: Vec<String> = items
        .iter()
        .filter_map(|it| match it {
            Item::Symbol(s) => Some(trim_lean_symbol(s)),
            Item::Placeholder(_) => None,
        })
        .collect();

    let (leading, lhs_prec, body_items): (bool, Option<u32>, &[Item]) = match &items[0] {
        Item::Placeholder(p) => (false, Some(p.unwrap_or(0)), &items[1..]),
        Item::Symbol(_) => (true, None, &items[..]),
    };
    let body_prims: Vec<Prim> = body_items
        .iter()
        .map(|it| match it {
            Item::Symbol(s) => Prim::Symbol(trim_lean_symbol(s)),
            Item::Placeholder(p) => Prim::Category {
                name: category.to_string(),
                rbp: p.unwrap_or(0),
            },
        })
        .collect();

    Some(NotationSpec {
        category: category.to_string(),
        kind_name,
        leading,
        prec,
        lhs_prec,
        tokens,
        body: Prim::Seq(body_prims),
    })
}

/// A `str` node's sole token carries the literal quoted text INCLUDING
/// the delimiting `"` characters (oracle dump: `{"a":"\" ⊕ \""}` for
/// source `" ⊕ "` — the five characters `"`, ` `, `⊕`, ` `, `"`).
/// Strips exactly those two delimiters; does NOT interpret any interior
/// backslash escapes — out of scope here for the same reason Task 3's
/// mangler leaves interior-whitespace handling unexercised (see
/// `mangle_symbol_atom`'s module-doc "Deliberately out of scope"): no
/// fixture/oracle dump this crate has ever produced contains one, and
/// a malformed/escaped atom is Task 9's formal remit, not this one's.
///
/// `pub(super)` (M3b2b Task 8): `grammar::surface` reuses this for the
/// SAME shape (`Lean.Parser.Syntax.atom`/`.nonReserved`'s wrapped `str`
/// child).
pub(super) fn strip_quotes(raw: &str) -> &str {
    raw.strip_prefix('"')
        .and_then(|s| s.strip_suffix('"'))
        .unwrap_or(raw)
}

/// `String.trimAscii` (`Char.isWhitespace`-only, see `is_lean_whitespace`'s
/// own doc comment) applied to a symbol atom's raw text — the same trim
/// `mangle_symbol_atom` applies before capitalizing, reused here (without
/// the capitalization step) for `NotationSpec::tokens`/`Prim::Symbol`,
/// which need the bare matchable token text, not a mangled kind-name
/// fragment.
pub fn trim_lean_symbol(raw: &str) -> String {
    raw.trim_matches(is_lean_whitespace).to_string()
}

/// First child NODE (not token) of `node` whose own kind name is
/// `name` — `SyntaxNode::children()` already skips tokens, so this is
/// a plain linear search, never a panic on an empty/short child list.
///
/// `pub(super)` (M3b2b Task 8): `grammar::surface` reuses this for the
/// same "find the optional-wrapper's populated inner node" navigation
/// (`namedName`, `Lean.Parser.precedence`, …).
pub(super) fn find_child(
    node: &SyntaxNode,
    name: &str,
    kinds: &KindInterner,
) -> Option<SyntaxNode> {
    node.children().find(|c| kinds.name(c.kind()) == name)
}

/// `node`'s first TOKEN child's raw text (rowan
/// `children_with_tokens()`, filtered to the `Token` arm) — every
/// self-wrapping leaf this module reads (`str`, `num`, a `mixfixKind`
/// alternative's own bare keyword atom) has exactly one.
///
/// `pub(super)` (M3b2b Task 8): `grammar::surface` reuses this for the
/// identical `str`-node shape its own stx-item walk reads.
pub(super) fn first_token_text(node: &SyntaxNode) -> Option<String> {
    node.children_with_tokens()
        .find_map(|el| el.into_token())
        .map(|t| t.text().to_string())
}

/// `Lean.Parser.precedence := ":" >> NumLit` (command_notation.rs's own
/// `precedence` production): find the wrapped `num` node and parse its
/// digit text. Never panics on a non-numeric/missing token — a failed
/// `str::parse` or absent child both fall through to `None`, same as
/// every other navigation step in this module.
///
/// `pub(super)` (M3b2b Task 8): `grammar::surface` reuses this for
/// `Syntax.cat`'s own optional `:prec` slot (identical `precedence`
/// shape).
pub(super) fn read_prec_num(precedence_node: &SyntaxNode, kinds: &KindInterner) -> Option<u32> {
    let num_node = find_child(precedence_node, "num", kinds)?;
    first_token_text(&num_node)?.parse().ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use NotationAtom::*;

    #[test]
    fn mangle_matches_oracle_kind_names() {
        // VALUES BELOW are copied from the Task 3 Step-1 oracle dump
        // (module doc above, probes 1/2) — the brief's illustrative
        // `⊕`/`~` strings, confirmed byte-exact (guillemets are
        // U+00AB/U+00BB) against a real dump using `⊗` in place of `⊕`
        // (top-level `⊕` already collides with `Init.Core`'s own
        // `infixr:30 " ⊕ " => Sum`, which is an unrelated
        // collision-avoidance mechanism this function doesn't
        // implement — see module doc's "Deliberately out of scope").
        assert_eq!(
            mangle_kind("term", &[Placeholder, Symbol(" ⊗ ".into()), Placeholder]),
            "«term_⊗_»"
        );
        assert_eq!(
            mangle_kind("term", &[Symbol("~".into()), Placeholder]),
            "«term~_»"
        );
    }

    /// Oracle dump probe 3 (module doc above): a notation whose mangled
    /// name happens to be a valid plain identifier prints WITHOUT
    /// guillemets, and a symbol atom's first character is capitalized —
    /// neither of which probes 1/2 exercise (⊗/~ have no case, and both
    /// need guillemets regardless).
    #[test]
    fn mangle_omits_guillemets_and_capitalizes_alpha_symbol_atoms() {
        assert_eq!(
            mangle_kind("term", &[Symbol("myOp".into()), Placeholder]),
            "termMyOp_"
        );
    }

    /// Oracle dump (Task 3 fix — mangler multi-atom + interior-ws
    /// coverage, module doc addendum): a notation with TWO cased
    /// keyword atoms and interior placeholders. Surface source dumped
    /// (via the module doc's `Lean.Elab.IO.processCommands`-driven
    /// scratch technique, pinned `lean` v4.32.0-rc1):
    /// ```text
    /// notation "if " c " then " t:100 => (c, t)
    /// example := if True then 1
    /// ```
    /// The `example`'s value's generated kind, observed byte-exact in
    /// the dump: `"termIf_Then_"` — no guillemets (already a valid
    /// plain identifier) AND both keyword atoms independently
    /// capitalized (`if ` → `If`, ` then ` → `Then`), confirming the
    /// per-atom capitalization branch fires more than once per call and
    /// that guillemet-omission still holds with >1 symbol atom (Probe 3
    /// in the module doc only exercised a single symbol atom).
    #[test]
    fn mangle_capitalizes_each_of_multiple_keyword_atoms() {
        assert_eq!(
            mangle_kind(
                "term",
                &[
                    Symbol("if ".into()),
                    Placeholder,
                    Symbol(" then ".into()),
                    Placeholder
                ]
            ),
            "termIf_Then_"
        );
    }

    /// Interior-whitespace-to-`_` coverage (Task 3 fix). NOT
    /// oracle-derived, unlike the test above — and deliberately so.
    ///
    /// Investigation finding: real Lean can never produce a `Symbol`
    /// atom whose TRIMMED contents still contain whitespace, because
    /// `Lean.Elab.Syntax`'s `isValidAtom` (pin v4.32.0-rc1,
    /// `Lean/Elab/Syntax.lean:250-259`) trims the same way this
    /// mangler does and then rejects the atom outright if any
    /// whitespace remains (`!(s.any Char.isWhitespace)`), throwing
    /// `"invalid atom"` and aborting the whole `notation`/`syntax`
    /// command — confirmed empirically: `notation "a b" x:100 => Not x`
    /// fails elaboration with exactly that error (scratch dump, same
    /// technique as above), so the command never registers and no
    /// generated kind ever exists to observe. `notation` delegates atom
    /// validation to this exact same code path (`Lean/Elab/Notation.lean`
    /// `public import`s `Lean.Elab.Syntax`; `expandNotationItemIntoSyntaxItem`
    /// converts each notation string atom into a `syntax`-command item,
    /// then `elabSyntax`'s `Term.toParserDescr` runs the identical
    /// `isValidAtom` gate), so this isn't a `notation`-specific quirk.
    ///
    /// `mkNameFromParserSyntax` (`Lean/Elab/Syntax.lean:334-357`, the
    /// function `mangle_symbol_atom` ports) DOES run its
    /// whitespace-to-`_` substitution — but it runs *before*
    /// `toParserDescr`'s validation, on the same syntax tree, and if
    /// that later validation throws, the name it computed is simply
    /// discarded along with the rest of the failed command. So the
    /// branch is real in the ported source, byte-confirmed to exist in
    /// `Lean/Elab/Syntax.lean`'s own text, but PROVABLY UNREACHABLE via
    /// any notation/syntax declaration Lean will actually accept — no
    /// oracle dump can ever exercise it, because no such dump can exist.
    ///
    /// Kept as a pure-function robustness test only (same rationale as
    /// `mangle_never_panics_on_degenerate_input` below), locking the
    /// mangler's own defined behavior for this synthetic input rather
    /// than an oracle-observed one.
    #[test]
    fn mangle_replaces_interior_whitespace_with_underscore() {
        assert_eq!(mangle_kind("term", &[Symbol("a b".into())]), "termA_b");
    }

    #[test]
    fn mangle_never_panics_on_degenerate_input() {
        assert_eq!(mangle_kind("", &[]), "«»");
        // An all-whitespace symbol atom trims away to nothing, leaving
        // `category` unchanged — which here is itself a valid plain
        // identifier, so no guillemets.
        assert_eq!(mangle_kind("term", &[Symbol("   ".into())]), "term");
        assert_eq!(
            mangle_kind("term", &[Symbol("»".into())]),
            // contains the closing guillemet itself: `escapePart`
            // can't safely escape it, so `Name.toStringWithSep` falls
            // back to the raw (unescaped) string.
            "term»"
        );
    }

    // ============================================================
    // `derive` (M3b1 Task 4). The task brief's own test sketch finds
    // the command node by outer kind `.contains("infixl")` — WRONG,
    // per this task's cross-task fact #1: `infixl`/`infixr`/`infix`/
    // `prefix`/`postfix` all share ONE outer kind
    // `Lean.Parser.Command.mixfix` (the FIXITY lives on the inner
    // `mixfixKind` child, which `derive` reads itself); only bare
    // `notation` gets its own outer kind. Fixed here to find the
    // command node by the real outer kind instead — confirmed against
    // a real oracle dump (this module's own probe, deleted before
    // commit) before writing any of these assertions.
    // ============================================================

    fn find_command(tree: &crate::tree::SyntaxTree, outer_kind: &str) -> SyntaxNode {
        tree.root()
            .children()
            .find(|c| tree.kinds.name(c.kind()) == outer_kind)
            .unwrap_or_else(|| panic!("no {outer_kind} command node in parsed tree"))
    }

    /// Test-only shim reproducing the OLD `derive`'s signature/contract
    /// (plain `Option<NotationSpec>`, `None` for anything that isn't a
    /// `notation`/`mixfix` production) over the new `derive_delta` —
    /// every `notation`/`mixfix` test below predates `GrammarDelta`
    /// (M3b2b Task 7) and asserts directly against `NotationSpec`
    /// fields; kept local to this test module (not part of the public
    /// API — see `derive_delta`'s own doc comment for why the real
    /// `derive` was removed rather than kept as a production wrapper)
    /// so those assertions don't all need rewriting to match on
    /// `GrammarDelta::Production` individually.
    fn derive(node: &SyntaxNode, kinds: &KindInterner) -> Option<NotationSpec> {
        match derive_delta(node, kinds) {
            Some(GrammarDelta::Production(spec)) => Some(spec),
            _ => None,
        }
    }

    #[test]
    fn derive_infixl_is_left_assoc_trailing() {
        let snap = crate::builtin::snapshot();
        let r = crate::parse_module("prelude\ninfixl:65 \" ⊕ \" => Sum\n", &snap);
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        let cmd = find_command(&r.tree, "Lean.Parser.Command.mixfix");
        let spec = derive(&cmd, &r.tree.kinds).expect("derives");
        assert_eq!(spec.category, "term");
        assert!(!spec.leading); // infixl ⇒ leading lhs placeholder ⇒ trailing parser
        assert_eq!(spec.prec, 65);
        assert_eq!(spec.lhs_prec, Some(65)); // infixl: left-assoc, lhs at the node's own prec
        assert_eq!(spec.tokens, vec!["⊕".to_string()]);
        assert!(spec.kind_name.starts_with("«term"));
        match &spec.body {
            Prim::Seq(ps) => match ps.as_slice() {
                [Prim::Symbol(s), Prim::Category { name, rbp }] => {
                    assert_eq!(s, "⊕");
                    assert_eq!(name, "term");
                    assert_eq!(*rbp, 66); // rhs at prec+1 (left-assoc: rhs binds tighter)
                }
                other => panic!("unexpected body shape: {other:?}"),
            },
            other => panic!("expected Prim::Seq, got {other:?}"),
        }
    }

    #[test]
    fn derive_infixr_right_assoc_bumps_lhs_prec() {
        let snap = crate::builtin::snapshot();
        let r = crate::parse_module("prelude\ninfixr:65 \" ⇒ \" => Arrow\n", &snap);
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        let cmd = find_command(&r.tree, "Lean.Parser.Command.mixfix");
        let spec = derive(&cmd, &r.tree.kinds).expect("derives");
        assert!(!spec.leading);
        assert_eq!(spec.prec, 65);
        assert_eq!(spec.lhs_prec, Some(66)); // infixr: lhs must be strictly tighter (prec+1)
        match &spec.body {
            Prim::Seq(ps) => match ps.as_slice() {
                [Prim::Symbol(s), Prim::Category { name, rbp }] => {
                    assert_eq!(s, "⇒");
                    assert_eq!(name, "term");
                    assert_eq!(*rbp, 65); // rhs at the node's own prec (right-assoc: rhs may chain)
                }
                other => panic!("unexpected body shape: {other:?}"),
            },
            other => panic!("expected Prim::Seq, got {other:?}"),
        }
    }

    /// Plain (non-associative) `infix` is absent from the brief's own
    /// mapping table — resolved here directly against the pinned
    /// toolchain's source (`Lean/Elab/Mixfix.lean:22-24`, pin
    /// v4.32.0-rc1): `infix:$prec $op => $f` expands to `notation:$prec
    /// lhs:$prec1 $op rhs:$prec1 => $f lhs rhs` (`prec1 := prec + 1`)
    /// — BOTH sides at `prec+1`, unlike infixl/infixr's asymmetric
    /// pair, so neither side can re-admit another `infix` at the same
    /// level without parens (non-associativity).
    #[test]
    fn derive_infix_is_nonassoc_both_sides_bumped() {
        let snap = crate::builtin::snapshot();
        let r = crate::parse_module("prelude\ninfix:65 \" ⊙ \" => Foo\n", &snap);
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        let cmd = find_command(&r.tree, "Lean.Parser.Command.mixfix");
        let spec = derive(&cmd, &r.tree.kinds).expect("derives");
        assert!(!spec.leading);
        assert_eq!(spec.prec, 65);
        assert_eq!(spec.lhs_prec, Some(66));
        match &spec.body {
            Prim::Seq(ps) => match ps.as_slice() {
                [Prim::Symbol(_), Prim::Category { rbp, .. }] => assert_eq!(*rbp, 66),
                other => panic!("unexpected body shape: {other:?}"),
            },
            other => panic!("expected Prim::Seq, got {other:?}"),
        }
    }

    #[test]
    fn derive_prefix_is_leading_no_lhs_prec() {
        let snap = crate::builtin::snapshot();
        let r = crate::parse_module("prelude\nprefix:100 \"~\" => Not\n", &snap);
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        let cmd = find_command(&r.tree, "Lean.Parser.Command.mixfix");
        let spec = derive(&cmd, &r.tree.kinds).expect("derives");
        assert!(spec.leading);
        assert_eq!(spec.prec, 100);
        assert_eq!(spec.lhs_prec, None);
        assert_eq!(spec.tokens, vec!["~".to_string()]);
        match &spec.body {
            Prim::Seq(ps) => match ps.as_slice() {
                [Prim::Symbol(s), Prim::Category { name, rbp }] => {
                    assert_eq!(s, "~");
                    assert_eq!(name, "term");
                    assert_eq!(*rbp, 100); // operand at the node's OWN prec, not prec+1
                }
                other => panic!("unexpected body shape: {other:?}"),
            },
            other => panic!("expected Prim::Seq, got {other:?}"),
        }
    }

    #[test]
    fn derive_postfix_is_trailing_no_rhs_operand() {
        let snap = crate::builtin::snapshot();
        let r = crate::parse_module("prelude\npostfix:100 \"!\" => Fact\n", &snap);
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        let cmd = find_command(&r.tree, "Lean.Parser.Command.mixfix");
        let spec = derive(&cmd, &r.tree.kinds).expect("derives");
        assert!(!spec.leading);
        assert_eq!(spec.prec, 100);
        assert_eq!(spec.lhs_prec, Some(100));
        match &spec.body {
            Prim::Seq(ps) => match ps.as_slice() {
                [Prim::Symbol(s)] => assert_eq!(s, "!"),
                other => panic!("unexpected body shape: {other:?}"),
            },
            other => panic!("expected Prim::Seq, got {other:?}"),
        }
    }

    #[test]
    fn derive_notation_with_explicit_precs_on_every_placeholder() {
        let snap = crate::builtin::snapshot();
        let r = crate::parse_module(
            "prelude\nnotation:70 a:71 \" ⊗ \" b:71 => Prod a b\n",
            &snap,
        );
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        let cmd = find_command(&r.tree, "Lean.Parser.Command.notation");
        let spec = derive(&cmd, &r.tree.kinds).expect("derives");
        assert_eq!(spec.category, "term");
        assert!(!spec.leading); // first item `a` is a placeholder
        assert_eq!(spec.prec, 70);
        assert_eq!(spec.lhs_prec, Some(71));
        assert_eq!(spec.tokens, vec!["⊗".to_string()]);
        match &spec.body {
            Prim::Seq(ps) => match ps.as_slice() {
                [Prim::Symbol(s), Prim::Category { name, rbp }] => {
                    assert_eq!(s, "⊗");
                    assert_eq!(name, "term");
                    assert_eq!(*rbp, 71);
                }
                other => panic!("unexpected body shape: {other:?}"),
            },
            other => panic!("expected Prim::Seq, got {other:?}"),
        }
    }

    /// Outer `:70` given explicitly, but NEITHER placeholder (`a`/`b`)
    /// has its own `:prec` — both default their own rbp/lhs_prec to
    /// `0` (`expandOptPrecedence`'s `getD 0`), independent of the
    /// outer node's own (here, explicit) precedence.
    #[test]
    fn derive_notation_defaults_lead_prec_and_zero_rbp_when_all_precs_omitted() {
        let snap = crate::builtin::snapshot();
        let r = crate::parse_module("prelude\nnotation:70 a \" ⊗ \" b => Prod a b\n", &snap);
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        let cmd = find_command(&r.tree, "Lean.Parser.Command.notation");
        let spec = derive(&cmd, &r.tree.kinds).expect("derives");
        assert!(!spec.leading);
        assert_eq!(spec.prec, 70); // outer prec WAS given explicitly here
        assert_eq!(spec.lhs_prec, Some(0)); // `a`'s own :prec omitted ⇒ default 0
        match &spec.body {
            Prim::Seq(ps) => match ps.as_slice() {
                [Prim::Symbol(_), Prim::Category { rbp, .. }] => assert_eq!(*rbp, 0),
                other => panic!("unexpected body shape: {other:?}"),
            },
            other => panic!("expected Prim::Seq, got {other:?}"),
        }
    }

    /// Fully atom-delimited notation (starts AND ends with a symbol,
    /// no outer `:prec` given): `isAtomLikeSyntax` ⇒ `MAX_PREC` default
    /// (`Lean/Elab/Syntax.lean:414`, pin v4.32.0-rc1).
    #[test]
    fn derive_notation_atom_like_defaults_to_max_prec() {
        let snap = crate::builtin::snapshot();
        let r = crate::parse_module("prelude\nnotation \"foo\" => Foo\n", &snap);
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        let cmd = find_command(&r.tree, "Lean.Parser.Command.notation");
        let spec = derive(&cmd, &r.tree.kinds).expect("derives");
        assert!(spec.leading);
        assert_eq!(spec.lhs_prec, None);
        assert_eq!(spec.prec, MAX_PREC);
        assert_eq!(spec.tokens, vec!["foo".to_string()]);
        match &spec.body {
            Prim::Seq(ps) => match ps.as_slice() {
                [Prim::Symbol(s)] => assert_eq!(s, "foo"),
                other => panic!("unexpected body shape: {other:?}"),
            },
            other => panic!("expected Prim::Seq, got {other:?}"),
        }
    }

    /// Symbol-first but placeholder-last (not atom-like on EITHER
    /// definition edge would matter — only both ends counts): no
    /// outer `:prec` given ⇒ `LEAD_PREC` default, multiple keyword
    /// atoms + interior placeholders all round-tripped through `body`
    /// in declaration order.
    #[test]
    fn derive_notation_not_atom_like_defaults_to_lead_prec() {
        let snap = crate::builtin::snapshot();
        let r = crate::parse_module("prelude\nnotation \"if \" c \" then \" t => c\n", &snap);
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        let cmd = find_command(&r.tree, "Lean.Parser.Command.notation");
        let spec = derive(&cmd, &r.tree.kinds).expect("derives");
        assert!(spec.leading); // first item is a symbol atom
        assert_eq!(spec.lhs_prec, None);
        assert_eq!(spec.prec, LEAD_PREC);
        assert_eq!(spec.tokens, vec!["if".to_string(), "then".to_string()]);
        match &spec.body {
            Prim::Seq(ps) => match ps.as_slice() {
                [Prim::Symbol(if_), Prim::Category { rbp: c_rbp, .. }, Prim::Symbol(then_), Prim::Category { rbp: t_rbp, .. }] =>
                {
                    assert_eq!(if_, "if");
                    assert_eq!(then_, "then");
                    assert_eq!(*c_rbp, 0);
                    assert_eq!(*t_rbp, 0);
                }
                other => panic!("unexpected body shape: {other:?}"),
            },
            other => panic!("expected Prim::Seq, got {other:?}"),
        }
    }

    /// Defensive `None`: a command whose outer kind is neither
    /// `mixfix` nor `notation`.
    #[test]
    fn derive_returns_none_for_non_notation_command() {
        let snap = crate::builtin::snapshot();
        let r = crate::parse_module("prelude\ndef foo := 1\n", &snap);
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        let cmd = find_command(&r.tree, "Lean.Parser.Command.declaration");
        assert!(derive(&cmd, &r.tree.kinds).is_none());
    }

    /// `mangle_private_kind`'s own doc comment has the oracle dump +
    /// source citation (Task 8, `NotationLocal.lean`'s gate run first
    /// surfaced this: `derive` was producing the PLAIN `mangle_kind`
    /// shape for a `local notation`, mismatching the real toolchain's
    /// `_private.0.«term★»`).
    #[test]
    fn mangle_private_kind_matches_oracle_local_notation_shape() {
        assert_eq!(
            mangle_private_kind("term", &[Symbol("★".into())]),
            "_private.0.«term★»"
        );
        // A plain-identifier-shaped local notation still gets the
        // `_private.0.` prefix, but the LAST component itself needs no
        // guillemets (mirrors `mangle_omits_guillemets_...` for the
        // non-local case).
        assert_eq!(
            mangle_private_kind("term", &[Symbol("myOp".into()), Placeholder]),
            "_private.0.termMyOp_"
        );
    }

    /// `derive`, end to end, on `local notation "★" => Sum` (Task 8's
    /// `NotationLocal.lean` fixture, oracle-confirmed against
    /// `dump_syntax_elab.lean`).
    #[test]
    fn derive_local_notation_uses_private_kind_name() {
        let snap = crate::builtin::snapshot();
        let r = crate::parse_module("local notation \"★\" => Sum\n", &snap);
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        let cmd = find_command(&r.tree, "Lean.Parser.Command.notation");
        let spec = derive(&cmd, &r.tree.kinds).expect("derives");
        assert_eq!(spec.kind_name, "_private.0.«term★»");
    }

    /// `scoped` notation is explicitly excluded from private mangling
    /// (`Lean/Elab/Syntax.lean:432`'s `attrKind matches \`(attrKind|
    /// local)` — `scoped` never matches that pattern; module doc's
    /// design-spec §7 citation). Not independently oracle-dumped for
    /// THIS test (no scoped fixture in the corpus — `scoped` is out of
    /// M3b1's scope per spec §7), but `is_local_attr_kind` returning
    /// `false` for `Lean.Parser.Term.scoped` is a direct, mechanical
    /// consequence of its own doc comment's condition, worth locking
    /// against a regression that widens the check to "any modifier".
    #[test]
    fn derive_scoped_notation_uses_plain_kind_name_not_private() {
        let snap = crate::builtin::snapshot();
        let r = crate::parse_module("scoped notation \"★\" => Sum\n", &snap);
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        let cmd = find_command(&r.tree, "Lean.Parser.Command.notation");
        let spec = derive(&cmd, &r.tree.kinds).expect("derives");
        assert_eq!(spec.kind_name, "«term★»");
    }

    // ============================================================
    // `contains_error_or_missing` / the Task 9 Step 3 guard.
    //
    // As `contains_error_or_missing`'s own doc comment explains,
    // this crate's interpreter can never actually PRODUCE a
    // `<missing>`/`<error>` node inside a subtree that reaches
    // `run_module`'s clean `Ok(())` arm — so exercising the guard
    // needs a HAND-BUILT tree (`tree::build_tree`, same technique
    // `tree.rs`'s own `events_build_a_lossless_tree` test uses), not
    // a real `crate::parse_module` call. `hand_built_mixfix` below
    // reproduces `command_notation.rs`'s own oracle-dumped `mixfix`
    // shape (module doc there: `infixl:65 " ⊕ " => Sum`) exactly,
    // parameterized over the final (RHS term) slot's own events, so
    // the SAME builder proves both directions: a valid RHS still
    // derives `Some` (the guard doesn't over-reject), and a
    // `<missing>`/`<error>` RHS derives `None` (the guard fires).
    // ============================================================

    /// Hand-builds `infixl:65"a"=>Sum`-shaped events (the exact child
    /// sequence `derive_mixfix` navigates — see `command_notation.rs`'s
    /// module-doc oracle dump), with the final RHS-term slot supplied
    /// by the caller. Not real lexable source text (offsets are
    /// synthetic, chosen only to keep every token's byte-slice valid)
    /// — irrelevant here since `derive` never re-lexes, only reads
    /// already-built node/token kinds and token text.
    fn hand_built_mixfix(rhs: Vec<crate::tree::Event>) -> crate::tree::SyntaxTree {
        use crate::kind::KIND_ATOM;
        use crate::kind::KIND_NULL;
        use crate::tree::{build_tree, Event};

        let src = "infixl:65\"a\"=>Sum";
        let mut it = KindInterner::new();
        let mixfix_k = it.intern("Lean.Parser.Command.mixfix");
        let attr_kind_k = it.intern("Lean.Parser.Term.attrKind");
        let infixl_k = it.intern("Lean.Parser.Command.infixl");
        let prec_k = it.intern("Lean.Parser.precedence");
        let num_k = it.intern("num");
        let str_k = it.intern("str");

        let mut events = vec![
            Event::Start(mixfix_k),
            Event::Start(KIND_NULL),
            Event::Finish, // optional docComment
            Event::Start(KIND_NULL),
            Event::Finish, // optional Term.attributes
            Event::Start(attr_kind_k),
            Event::Start(KIND_NULL),
            Event::Finish, // scoped/local absent
            Event::Finish, // attrKind
            Event::Start(infixl_k),
            Event::Token {
                kind: KIND_ATOM,
                offset: 0,
                len: 6,
            }, // "infixl"
            Event::Finish, // mixfixKind
            Event::Start(prec_k),
            Event::Token {
                kind: KIND_ATOM,
                offset: 6,
                len: 1,
            }, // ":"
            Event::Start(num_k),
            Event::Token {
                kind: KIND_ATOM,
                offset: 7,
                len: 2,
            }, // "65"
            Event::Finish, // num
            Event::Finish, // precedence
            Event::Start(KIND_NULL),
            Event::Finish, // optional namedName
            Event::Start(KIND_NULL),
            Event::Finish, // optional namedPrio
            Event::Start(str_k),
            Event::Token {
                kind: KIND_ATOM,
                offset: 9,
                len: 3,
            }, // "\"a\""
            Event::Finish, // str
            Event::Token {
                kind: KIND_ATOM,
                offset: 12,
                len: 2,
            }, // "=>"
        ];
        events.extend(rhs);
        events.push(Event::Finish); // mixfix

        build_tree(src, &events, std::sync::Arc::new(it))
    }

    /// Baseline: `hand_built_mixfix` with a REAL ident RHS derives
    /// `Some` — proves the guard tests below fail because of the
    /// injected `<missing>`/`<error>`, not because the synthetic tree
    /// is shaped wrong some other way.
    #[test]
    fn hand_built_mixfix_with_valid_rhs_still_derives_some() {
        use crate::kind::KIND_IDENT;
        use crate::tree::Event;

        let tree = hand_built_mixfix(vec![Event::Token {
            kind: KIND_IDENT,
            offset: 14,
            len: 3,
        }]); // "Sum"
        assert!(
            derive(&tree.root(), &tree.kinds).is_some(),
            "a structurally complete mixfix subtree must still derive"
        );
    }

    /// Task 9 Step 3's focused test: a `<missing>` leaf in the RHS
    /// term slot — a required structural slot (`command_notation.rs`'s
    /// oracle shape: `.. "=>" term`) — must make `derive` return
    /// `None`, even though nothing else in the subtree is malformed.
    #[test]
    fn derive_returns_none_when_rhs_term_slot_is_missing() {
        use crate::tree::Event;

        let tree = hand_built_mixfix(vec![Event::Missing]);
        assert!(
            derive(&tree.root(), &tree.kinds).is_none(),
            "a <missing> RHS term must not derive a NotationSpec"
        );
    }

    /// Same, but the RHS slot is an `<error>` node (`KIND_ERROR` — the
    /// kind `Ps::recover_command` wraps swept tokens in) instead of a
    /// bare `<missing>` leaf — covers the OTHER kind the brief names
    /// (`KIND_ERROR`/`KIND_MISSING`), not just one of the two.
    #[test]
    fn derive_returns_none_when_rhs_term_slot_is_an_error_node() {
        use crate::kind::{KIND_ATOM, KIND_ERROR};
        use crate::tree::Event;

        let tree = hand_built_mixfix(vec![
            Event::Start(KIND_ERROR),
            Event::Token {
                kind: KIND_ATOM,
                offset: 14,
                len: 3,
            },
            Event::Finish,
        ]);
        assert!(
            derive(&tree.root(), &tree.kinds).is_none(),
            "an <error> RHS term must not derive a NotationSpec"
        );
    }

    /// The guard recurses, not just a shallow top-level scan: a
    /// `<missing>` nested TWO levels deep (inside `precedence`'s own
    /// `num` child, not a direct child of the outer `mixfix` node)
    /// must still be caught. RHS term is a real, valid ident here —
    /// the ONLY malformed slot is the precedence's digit.
    #[test]
    fn derive_returns_none_when_a_nested_slot_is_missing() {
        use crate::kind::{KIND_ATOM, KIND_IDENT, KIND_NULL};
        use crate::tree::{build_tree, Event};

        let src = "infixl:\"a\"=>Sum";
        let mut it = KindInterner::new();
        let mixfix_k = it.intern("Lean.Parser.Command.mixfix");
        let attr_kind_k = it.intern("Lean.Parser.Term.attrKind");
        let infixl_k = it.intern("Lean.Parser.Command.infixl");
        let prec_k = it.intern("Lean.Parser.precedence");
        let num_k = it.intern("num");
        let str_k = it.intern("str");
        let events = vec![
            Event::Start(mixfix_k),
            Event::Start(KIND_NULL),
            Event::Finish,
            Event::Start(KIND_NULL),
            Event::Finish,
            Event::Start(attr_kind_k),
            Event::Start(KIND_NULL),
            Event::Finish,
            Event::Finish,
            Event::Start(infixl_k),
            Event::Token {
                kind: KIND_ATOM,
                offset: 0,
                len: 6,
            },
            Event::Finish,
            Event::Start(prec_k),
            Event::Token {
                kind: KIND_ATOM,
                offset: 6,
                len: 1,
            },
            Event::Start(num_k),
            Event::Missing, // <-- the ONLY malformed slot, 2 levels deep
            Event::Finish,
            Event::Finish,
            Event::Start(KIND_NULL),
            Event::Finish,
            Event::Start(KIND_NULL),
            Event::Finish,
            Event::Start(str_k),
            Event::Token {
                kind: KIND_ATOM,
                offset: 7,
                len: 3,
            },
            Event::Finish,
            Event::Token {
                kind: KIND_ATOM,
                offset: 10,
                len: 2,
            },
            Event::Token {
                kind: KIND_IDENT,
                offset: 12,
                len: 3,
            },
            Event::Finish,
        ];
        let tree = build_tree(src, &events, std::sync::Arc::new(it));
        assert!(
            derive(&tree.root(), &tree.kinds).is_none(),
            "a <missing> nested inside `precedence`'s own `num` child must still be caught"
        );
    }

    // ============================================================
    // M3b2b Task 8 preliminary (controller-added, from Task 7's
    // review): lock `derive_delta`'s `declare_syntax_cat`
    // `(behavior := ..)` → `LeadingIdentBehavior` mapping with a real
    // parse, mirroring `parse.rs`'s own
    // `declare_syntax_cat_creates_a_quotable_category` test's technique
    // (`crate::parse_module` + `crate::builtin::snapshot()`, not a
    // hand-built tree) — the oracle-accepted `(behavior := symbol)`/
    // `(behavior := both)` surface is `command_syntax.rs`'s own ported
    // `cat_behavior` production (module doc there: `declare_syntax_cat
    // gadget (behavior := symbol)` dump citation), reused verbatim here.
    // ============================================================

    #[test]
    fn derive_delta_maps_declare_syntax_cat_behavior_clause() {
        let snap = crate::builtin::snapshot();

        let r = crate::parse_module("declare_syntax_cat widgetish\n", &snap);
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        let cmd = find_command(&r.tree, "Lean.Parser.Command.syntaxCat");
        match derive_delta(&cmd, &r.tree.kinds) {
            Some(GrammarDelta::NewCategory { name, behavior }) => {
                assert_eq!(name, "widgetish");
                assert_eq!(behavior, LeadingIdentBehavior::Default);
            }
            other => panic!("expected NewCategory, got {other:?}"),
        }

        let r = crate::parse_module("declare_syntax_cat gadget (behavior := symbol)\n", &snap);
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        let cmd = find_command(&r.tree, "Lean.Parser.Command.syntaxCat");
        match derive_delta(&cmd, &r.tree.kinds) {
            Some(GrammarDelta::NewCategory { name, behavior }) => {
                assert_eq!(name, "gadget");
                assert_eq!(behavior, LeadingIdentBehavior::Symbol);
            }
            other => panic!("expected NewCategory, got {other:?}"),
        }

        let r = crate::parse_module("declare_syntax_cat widget2 (behavior := both)\n", &snap);
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        let cmd = find_command(&r.tree, "Lean.Parser.Command.syntaxCat");
        match derive_delta(&cmd, &r.tree.kinds) {
            Some(GrammarDelta::NewCategory { name, behavior }) => {
                assert_eq!(name, "widget2");
                assert_eq!(behavior, LeadingIdentBehavior::Both);
            }
            other => panic!("expected NewCategory, got {other:?}"),
        }
    }

    /// M3b2b final review (Important 1): the `stx` `sepBy`/`sepBy1`
    /// surface carries an OPTIONAL custom-`psep` slot
    /// (`surface.rs`'s `children.get(2)`). The 2-arg form
    /// (`sepBy(p, ", ")`) leaves it empty and derives a real
    /// `Prim::SepBy`; a POPULATED psep (`sepBy(p, ", ", q)`) is an
    /// unhandled combinator — skip-and-record (never guess) demands the
    /// whole production derive NOTHING rather than silently dropping the
    /// psep into a wrong `Prim::SepBy`.
    #[test]
    fn sepby_with_custom_psep_skips_and_records() {
        let snap = crate::builtin::snapshot();

        // 2-arg form: psep empty ⇒ a real trailing `Prim::SepBy`.
        let r = crate::parse_module("syntax \"sepp\" sepBy(term, \", \") : term\n", &snap);
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        let cmd = find_command(&r.tree, "Lean.Parser.Command.syntax");
        let spec = derive(&cmd, &r.tree.kinds).expect("2-arg sepBy derives a production");
        match &spec.body {
            Prim::Seq(ps) => assert!(
                matches!(ps.last(), Some(Prim::SepBy { .. })),
                "expected a trailing Prim::SepBy, got {:?}",
                spec.body
            ),
            other => panic!("expected a Prim::Seq body, got {other:?}"),
        }

        // Populated custom psep (3rd arg `term`): unhandled ⇒ the whole
        // production derives NOTHING (the declaration itself is still
        // well-formed `stx` and parses cleanly).
        let r = crate::parse_module("syntax \"sepp\" sepBy(term, \", \", term) : term\n", &snap);
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        let cmd = find_command(&r.tree, "Lean.Parser.Command.syntax");
        assert!(
            derive_delta(&cmd, &r.tree.kinds).is_none(),
            "a populated custom psep must skip-and-record (derive None), not drop the psep"
        );
    }
}
