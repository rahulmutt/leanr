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

use crate::lex::{is_id_first, is_id_rest};

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
    let mut base = String::from(category);
    for atom in atoms {
        match atom {
            NotationAtom::Placeholder => base.push('_'),
            NotationAtom::Symbol(s) => base.push_str(&mangle_symbol_atom(s)),
        }
    }
    escape_name_component(&base)
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
fn mangle_symbol_atom(raw: &str) -> String {
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
fn escape_name_component(s: &str) -> String {
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

fn needs_no_escape(s: &str) -> bool {
    let mut chars = s.chars();
    match chars.next() {
        Some(first) => is_id_first(first) && chars.all(is_id_rest),
        None => false,
    }
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
}
