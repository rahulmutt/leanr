//! Source-level derivation for the general `syntax`-command surface
//! (M3b2b Task 8) — the twin of `leanr_grammar::descr` (which walks the
//! same combinators as decoded olean `ParserDescr` Exprs, i.e.
//! POST-elaboration). Skip-and-record: any item outside the walk
//! returns `None` and the WHOLE command derives nothing — see
//! `derive_surface`'s own doc comment for the exact discipline.
//!
//! ORACLE-PORT of `Lean/Elab/Syntax.lean` + `Lean/Elab/Macro.lean` (pin
//! v4.32.0-rc1) — every shape/rule below is read directly off those
//! files (`Term.toParserDescr`'s `process`/`checkLeftRec`/
//! `processNullaryOrCat`/`isAtomLikeSyntax`/`mkNameFromParserSyntax`,
//! `Command.elabSyntax`/`elabSyntaxAbbrev`, `elabMacro`), not just the
//! task brief's illustrative sketch — see individual functions' doc
//! comments for where this module CORRECTS or GENERALIZES that sketch
//! after reading the real source (`stx_item`'s `Syntax.cat` arm and
//! `mangle_items`/`mangle_visit` are the two places this mattered).
//!
//! **A critical divergence from `leanr_grammar::descr.rs`'s otherwise-
//! analogous `ParserDescr.cat` arm**: `descr.rs` interprets an
//! ALREADY-ELABORATED `.olean` constant, where the elaborator (`Lean/
//! Elab/Syntax.lean`'s `processNullaryOrCat`) has ALREADY decided
//! whether a bare identifier item names a real CATEGORY or a builtin
//! PARSER ALIAS (`num`/`str`/`char`/`ident`/`scientific` — the very
//! table `alias.rs`'s own module doc calls "one pinned table, two
//! consumers") — an alias resolves to `ParserDescr.const`/`.unary`/
//! `.binary` at COMPILE time, so `ParserDescr.cat` in a decoded olean
//! NEVER represents an alias reference, making `descr.rs`'s
//! unconditional `Prim::Category` mapping correct there. THIS module
//! walks the RAW, PRE-elaboration `Syntax.cat` node (`ident >>
//! optPrecedence`, `command_syntax.rs`'s own production) — the SAME
//! alias-vs-category decision `processNullaryOrCat` makes has NOT
//! happened yet, so `stx_item`'s own `Syntax.cat` arm must make it
//! itself (see that function's doc comment) or `syntax num : widgetish`
//! would wrongly try to recurse into a nonexistent "num" CATEGORY
//! instead of parsing a literal number — confirmed load-bearing by
//! `StxDeclareUse.lean`'s own `#check grab[42]` line, which requires
//! exactly this resolution to parse at all.

use std::sync::Arc;

use super::alias::{self, AliasPrim};
use super::notation::{
    escape_name_component, find_child, first_ident_token_text, first_token_text,
    mangle_symbol_atom, private_kind_name, qualify_kind_name, read_prec_num,
    spec_scope_from_attr_kind, strip_quotes, trim_lean_symbol, GrammarDelta, NamingCtx,
    NotationSpec,
};
use super::{walk_symbols, Prim, SpecScope, LEAD_PREC, MAX_PREC};
use crate::kind::{KindInterner, KIND_IDENT};
use crate::tree::SyntaxNode;

/// Derivation for the general command surface. `None` = this command
/// derives nothing (shape-only command, or an item the walk cannot
/// interpret — skip-and-record discipline: the command still parsed;
/// a use-site of the underivable syntax diverges and stays off the
/// pass-list, exactly like an uninterpretable imported entry, M3b2a's
/// own discipline). Dispatch mirrors `notation.rs::derive_delta`'s own
/// outer-kind match, one arm per kind `command_syntax.rs`'s module doc
/// pins against a real oracle dump — no speculative arms.
pub fn derive_surface(
    node: &SyntaxNode,
    kinds: &KindInterner,
    ctx: NamingCtx<'_>,
) -> Option<GrammarDelta> {
    let name = kinds.name(node.kind());
    match name {
        "Lean.Parser.Command.syntax" => derive_syntax_cmd(node, kinds, ctx),
        "Lean.Parser.Command.syntaxAbbrev" => derive_syntax_abbrev(node, kinds),
        "Lean.Parser.Command.macro" => derive_macro_cmd(node, kinds, ctx),
        // M3b3 Task 10: real derivation, rejoining `GRAMMAR_GROWING_KINDS`
        // (`parse.rs`'s own const doc comment) — pinned against a real
        // toolchain dump (`StxElab.lean`/`.stx.jsonl`, oracle v4.32.0-rc1),
        // not the M3b2b Task 8 recorded skip this comment used to describe.
        "Lean.Parser.Command.elab" => derive_elab_cmd(node, kinds, ctx),
        "Lean.Parser.Command.binderPredicate" => derive_binder_predicate(node, kinds, ctx),
        // Shape-only (`command_syntax.rs`'s own module doc): parses
        // fine, derives nothing — `macro_rules`/`elab_rules` pattern-
        // match against an ALREADY-registered kind, they never
        // register one themselves (`GRAMMAR_GROWING_KINDS`'s own doc
        // comment: these stay OFF that list).
        "Lean.Parser.Command.macro_rules" | "Lean.Parser.Command.elab_rules" => None,
        _ => None,
    }
}

/// `elab`'s oracle shape (M3b3 Task 10, `StxElab.stx.jsonl`'s own dump,
/// oracle v4.32.0-rc1): node-only children are BYTE-IDENTICAL in count
/// and order to `macro`'s own (`derive_macro_cmd`'s doc comment) —
/// `Lean/Parser/Syntax.lean:125-129`'s `elabArg := macroArg` and
/// `elabTail`'s combinator (`atomic (" : " ident (optional (" <= "
/// ident)))` sequenced with `darrow` then `withPosition termParser`)
/// mirror `macroArg`/`macroTail` exactly except for the tail's own kind
/// name and its extra (ignored) `<= expectedType` binder slot. That
/// slot is nested ONE level inside its own `null` wrapper (the
/// `optional` around `" <= " ident`), so it never appears as a direct
/// token child of the tail node — `last_ident_token_text` (a direct,
/// non-descending scan) reads the real target-category ident
/// (`term`/`tactic`/`command`/…) whether or not `<= expectedType` is
/// present, unchanged from
/// `derive_macro_cmd`'s own use of it. `local elab`/`scoped elab` are
/// real Mathlib patterns (`Mathlib/Tactic/Contrapose.lean`,
/// `Mathlib/Geometry/Manifold/Notation.lean`) — `StxElab.lean`'s own
/// `local elab` line pins that `spec_scope_from_attr_kind` (the same
/// gate `derive_macro_cmd`/`derive_syntax_cmd` already use) applies
/// here unchanged too (dump-confirmed: `#check wobello` resolves to
/// `_private.0.termWobello`).
///
/// Grammar-side only (this task's remit, `derive_surface`'s own doc
/// comment): the RHS elaborator body (`elabTail`'s own trailing term)
/// is read NEVER, exactly like `derive_macro_cmd` never reads
/// `macroRhs` — `elab_rules`'s own companion registration (shape-only,
/// `derive_surface`'s `"elab_rules"` arm) is where real Lean threads
/// that body to a handler; out of scope here (M4 elaborator semantics).
fn derive_elab_cmd(
    node: &SyntaxNode,
    kinds: &KindInterner,
    ctx: NamingCtx<'_>,
) -> Option<GrammarDelta> {
    let children: Vec<SyntaxNode> = node.children().collect();
    let attr_kind_pos = children
        .iter()
        .position(|c| kinds.name(c.kind()) == "Lean.Parser.Term.attrKind")?;
    let scope = spec_scope_from_attr_kind(&children[attr_kind_pos], kinds, ctx);
    let prec_wrapper = children.get(attr_kind_pos + 1)?;
    let explicit_prec = find_child(prec_wrapper, "Lean.Parser.precedence", kinds)
        .and_then(|pn| read_prec_num(&pn, kinds));
    let named_name_wrapper = children.get(attr_kind_pos + 2)?;
    let explicit_name = named_name_ident(named_name_wrapper, kinds);
    let args_wrapper = children.get(attr_kind_pos + 4)?;
    let elab_tail = children.get(attr_kind_pos + 5)?;
    if kinds.name(elab_tail.kind()) != "Lean.Parser.Command.elabTail" {
        return None;
    }
    let category = last_ident_token_text(elab_tail)?;

    let mut item_nodes = Vec::new();
    for arg_node in args_wrapper.children() {
        if kinds.name(arg_node.kind()) != "Lean.Parser.Command.macroArg" {
            return None;
        }
        let arg_children: Vec<SyntaxNode> = arg_node.children().collect();
        item_nodes.push(arg_children.get(1)?.clone());
    }
    build_from_items(
        &category,
        &item_nodes,
        explicit_prec,
        explicit_name,
        scope,
        kinds,
        ctx.current_ns,
    )
}

/// `binderPredicate`'s oracle shape (M3b3 Task 10, `StxElab.stx.jsonl`'s
/// own dump, oracle v4.32.0-rc1): `Lean/Parser/Syntax.lean:137-139`'s
///
/// ```text
/// optional docComment >> optional Term.attributes >> optional Term.attrKind >>
/// "binder_predicate" >> optNamedName >> optNamedPrio >> ppSpace >> ident >>
/// many (ppSpace >> macroArg) >> " => " >> termParser
/// ```
///
/// has NO `optPrecedence` slot at all (unlike `syntax`/`macro`/`elab`),
/// and — the one genuine structural divergence — its `attrKind` slot is
/// DOUBLE-wrapped: `optional Term.attrKind`, not the bare `Term.attrKind`
/// every other attrKind-anchored command here has. `Term.attrKind`
/// itself is `leading_parser optional (scoped <|> local)`
/// (`Lean/Parser/Term.lean:586`) — a parser that can never fail — so the
/// OUTER `optional` around it always takes the "matched" branch: the
/// wrapper is never truly absent, but it IS one extra `null` layer a
/// direct `attrKind`-kind-name child search (`derive_syntax_cmd`/
/// `derive_macro_cmd`/`derive_elab_cmd`'s own anchor) would never find.
/// So the anchor here is "the null child whose OWN child is
/// `Term.attrKind`", one `find_child` deeper.
///
/// Node-only children, in order: `[null(doc), null(attrs),
/// null(attrKind-wrapper), null(namedName?), null(namedPrio?),
/// null(many macroArg), <ignored RHS term node>]` — the bound `ident`
/// (`x` in `Init/BinderPredicates.lean`'s own `binder_predicate x " > "
/// y:term => ...`, `wbx` in the dump fixture) is a bare TOKEN, invisible
/// to `.children()`, and is never part of the registered production
/// (ORACLE-PORT `elabBinderPred`, `Lean/Elab/BinderPredicates.lean`: the
/// generated `syntax ... : binderPred` command's own item list is built
/// from `args` alone — the ident is threaded to the companion
/// `macro_rules` registration instead, out of this task's grammar-only
/// remit, same as `derive_elab_cmd`'s RHS). Target category is the
/// oracle's own `declare_syntax_cat binderPred`
/// (`Init/BinderPredicates.lean:22`) — confirmed from source AND the
/// dump, not the brief's placeholder guess.
fn derive_binder_predicate(
    node: &SyntaxNode,
    kinds: &KindInterner,
    ctx: NamingCtx<'_>,
) -> Option<GrammarDelta> {
    let children: Vec<SyntaxNode> = node.children().collect();
    let attr_wrapper_pos = children
        .iter()
        .position(|c| find_child(c, "Lean.Parser.Term.attrKind", kinds).is_some())?;
    let attr_kind = find_child(
        &children[attr_wrapper_pos],
        "Lean.Parser.Term.attrKind",
        kinds,
    )?;
    let scope = spec_scope_from_attr_kind(&attr_kind, kinds, ctx);
    let named_name_wrapper = children.get(attr_wrapper_pos + 1)?;
    let explicit_name = named_name_ident(named_name_wrapper, kinds);
    let args_wrapper = children.get(attr_wrapper_pos + 3)?;

    let mut item_nodes = Vec::new();
    for arg_node in args_wrapper.children() {
        if kinds.name(arg_node.kind()) != "Lean.Parser.Command.macroArg" {
            return None;
        }
        let arg_children: Vec<SyntaxNode> = arg_node.children().collect();
        item_nodes.push(arg_children.get(1)?.clone());
    }
    build_from_items(
        "binderPred",
        &item_nodes,
        None,
        explicit_name,
        scope,
        kinds,
        ctx.current_ns,
    )
}

/// `syntax`'s oracle shape (`command_syntax.rs`'s module doc,
/// `StxShapes.stx.jsonl`/`StxDeclareUse.stx.jsonl`'s own dumps):
/// node-only children (the bare `"syntax"` keyword atom and the
/// trailing target-category ident are both TOKENS, invisible to
/// `SyntaxNode::children()` — same token/node split `notation.rs`'s
/// `derive_notation` doc comment already establishes) are `[null(doc),
/// null(attrs), attrKind, null(precedence?), null(namedName?),
/// null(namedPrio?), null(many1 stx-items)]` — 7 total, anchored off
/// `attrKind`'s own unique kind name exactly like `derive_mixfix`/
/// `derive_notation` (so a populated doc-comment slot can't shift
/// anything). The trailing target-category ident is read straight off
/// the OUTER node's own direct tokens (`last_ident_token_text`), not a
/// node child at all.
///
/// M3b3 Task 3 (oracle-confirmed, `StxLocal.lean`): `local syntax`/
/// `local macro` derive the PRIVATE kind name, the identical
/// `mkPrivateName` gate `notation.rs`'s `is_local_attr_kind`/
/// `private_kind_name` already pin for `local notation`/`local
/// infixl`/… (`Lean/Elab/Syntax.lean:432-436`'s `elabSyntax` applies it
/// uniformly regardless of which surface the declaration came through
/// — this function and `derive_macro_cmd` both locate the same
/// `attrKind` anchor already used for the prec/name slots below, so
/// reading `is_local` off it here is free).
fn derive_syntax_cmd(
    node: &SyntaxNode,
    kinds: &KindInterner,
    ctx: NamingCtx<'_>,
) -> Option<GrammarDelta> {
    let children: Vec<SyntaxNode> = node.children().collect();
    let attr_kind_pos = children
        .iter()
        .position(|c| kinds.name(c.kind()) == "Lean.Parser.Term.attrKind")?;
    let scope = spec_scope_from_attr_kind(&children[attr_kind_pos], kinds, ctx);
    let prec_wrapper = children.get(attr_kind_pos + 1)?;
    let explicit_prec = find_child(prec_wrapper, "Lean.Parser.precedence", kinds)
        .and_then(|pn| read_prec_num(&pn, kinds));
    let named_name_wrapper = children.get(attr_kind_pos + 2)?;
    let explicit_name = named_name_ident(named_name_wrapper, kinds);
    let items_wrapper = children.get(attr_kind_pos + 4)?;
    let category = last_ident_token_text(node)?;

    let item_nodes: Vec<SyntaxNode> = items_wrapper.children().collect();
    build_from_items(
        &category,
        &item_nodes,
        explicit_prec,
        explicit_name,
        scope,
        kinds,
        ctx.current_ns,
    )
}

/// `syntaxAbbrev` (ORACLE `elabSyntaxAbbrev`, `Lean/Elab/Syntax.lean`):
/// defines a NAMED, standalone `ParserDescr` constant
/// (`ParserDescr.nodeWithAntiquot (toString declName) stxNodeKind
/// val`) — critically, it registers NO production into any CATEGORY at
/// all. The constant is only ever reachable by a LATER `syntax`/
/// `notation` declaration NAMING it — an ident that resolves via
/// `elabParserName?`'s `.parser (isDescr := true)` branch
/// (`processNullaryOrCat`), a THIRD resolution alongside `.category`/
/// `.alias` that `GrammarDelta` has no representation for at all
/// (only `Production`, into an existing category, and `NewCategory`).
/// So this is unconditionally skip-and-record: `StxShapes.lean`'s own
/// `syntax myNum := num` line (never referenced from elsewhere in that
/// fixture) confirms this has no observable category-registration
/// effect this crate's grammar model can represent yet. A real
/// reference site (`syntax "foo" myNum : term`) would need a
/// name-to-parser-fragment table this task doesn't build — recorded
/// gap for a future task, not silently wrong.
fn derive_syntax_abbrev(_node: &SyntaxNode, _kinds: &KindInterner) -> Option<GrammarDelta> {
    None
}

/// `macro`'s oracle shape (`command_syntax.rs`'s module doc,
/// `QuotMacroRules.stx.jsonl`'s own dump): node-only children mirror
/// `syntax`'s exactly (attrKind-anchored `[null(doc), null(attrs),
/// attrKind, null(precedence?), null(namedName?), null(namedPrio?)]`
/// prefix, `command_syntax.rs` builds all three optional slots the
/// identical way) except the last TWO slots: `null(many1 macroArg)`
/// then a real `Command.macroTail` NODE (not a bare trailing ident —
/// its own sole node child is `macroRhs`; its target-category ident is
/// a bare TOKEN, read via `last_ident_token_text` applied to the
/// `macroTail` node itself, not the outer `macro` node).
///
/// ORACLE-PORT `elabMacro` (`Lean/Elab/Macro.lean`): a `macro` command
/// literally SYNTHESIZES a `syntax` command from its own `macroArg*`
/// list (`expandMacroArg` unwraps each `macroArg`'s own `stx` item into
/// one `stxPart`) — mirrored here by extracting each `macroArg`'s
/// second node child (its wrapped stx item; the first is the optional
/// `ident ":"` binding-name prefix, irrelevant to the PARSER shape,
/// only to the RHS pattern `elabMacro` builds) and feeding the same
/// flat item list into `build_from_items`, exactly the tail
/// `derive_syntax_cmd` uses. The macro's RHS (`macroTail`'s
/// `macroRhs`) is read NEVER — ignored entirely per this task's brief:
/// the companion `macro_rules` registration `elabMacro` also
/// synthesizes is shape-only (`derive_surface`'s own `macro_rules`
/// arm), Task 8's remit is the PARSER side only.
fn derive_macro_cmd(
    node: &SyntaxNode,
    kinds: &KindInterner,
    ctx: NamingCtx<'_>,
) -> Option<GrammarDelta> {
    let children: Vec<SyntaxNode> = node.children().collect();
    let attr_kind_pos = children
        .iter()
        .position(|c| kinds.name(c.kind()) == "Lean.Parser.Term.attrKind")?;
    let scope = spec_scope_from_attr_kind(&children[attr_kind_pos], kinds, ctx);
    let prec_wrapper = children.get(attr_kind_pos + 1)?;
    let explicit_prec = find_child(prec_wrapper, "Lean.Parser.precedence", kinds)
        .and_then(|pn| read_prec_num(&pn, kinds));
    let named_name_wrapper = children.get(attr_kind_pos + 2)?;
    let explicit_name = named_name_ident(named_name_wrapper, kinds);
    let args_wrapper = children.get(attr_kind_pos + 4)?;
    let macro_tail = children.get(attr_kind_pos + 5)?;
    if kinds.name(macro_tail.kind()) != "Lean.Parser.Command.macroTail" {
        return None;
    }
    let category = last_ident_token_text(macro_tail)?;

    let mut item_nodes = Vec::new();
    for arg_node in args_wrapper.children() {
        if kinds.name(arg_node.kind()) != "Lean.Parser.Command.macroArg" {
            return None;
        }
        let arg_children: Vec<SyntaxNode> = arg_node.children().collect();
        item_nodes.push(arg_children.get(1)?.clone());
    }
    build_from_items(
        &category,
        &item_nodes,
        explicit_prec,
        explicit_name,
        scope,
        kinds,
        ctx.current_ns,
    )
}

/// Shared tail of `derive_syntax_cmd`/`derive_macro_cmd`: an ordered
/// list of TOP-LEVEL stx-item nodes (already extracted from whichever
/// command's own layout, `macro`'s own `ident:`-prefix already
/// stripped) + the target category + optional explicit `:prec`/`(name
/// := ..)` overrides -> a `NotationSpec`.
///
/// ORACLE-PORT `checkLeftRec` + `processSeq` (`Lean/Elab/Syntax.lean`):
/// the FIRST item, and ONLY the first, is checked for being a
/// same-category `Syntax.cat` placeholder — if so, this is a Pratt
/// "trailing" entry (lhs precedence = that item's own `:prec`,
/// defaulting `0`), and the item is STRIPPED (never a body child).
/// Mirrors `notation.rs`'s `build_spec`, generalized to `stx_item`-built
/// `Prim`s instead of a flat `Item` enum.
fn build_from_items(
    category: &str,
    item_nodes: &[SyntaxNode],
    explicit_prec: Option<u32>,
    explicit_name: Option<String>,
    scope: SpecScope,
    kinds: &KindInterner,
    current_ns: &str,
) -> Option<GrammarDelta> {
    if item_nodes.is_empty() {
        return None;
    }
    // Only `local` privatizes the kind name (`scoped` does not) — the
    // `Local` variant is the privatize gate, same as `notation.rs`'s
    // `build_spec`.
    let is_local = matches!(scope, SpecScope::Local { .. });
    let first = &item_nodes[0];
    let (leading, lhs_prec, body_nodes): (bool, Option<u32>, &[SyntaxNode]) =
        if kinds.name(first.kind()) == "Lean.Parser.Syntax.cat" {
            let (cat_name, rbp) = syntax_cat_name_and_rbp(first, kinds)?;
            if cat_name == category {
                (false, Some(rbp), &item_nodes[1..])
            } else {
                (true, None, item_nodes)
            }
        } else {
            (true, None, item_nodes)
        };

    let body_prims: Vec<Prim> = body_nodes
        .iter()
        .map(|n| stx_item(n, kinds))
        .collect::<Option<_>>()?;

    // M3b3 Task 2: both arms qualify — an explicit `(name := ..)`
    // override also gets `currNamespace ++` prepended (`stxNodeKind :=
    // currNamespace ++ name` applies uniformly in `elabSyntax`/
    // `elabMacro`, regardless of whether the name came from
    // `mkNameFromParserSyntax` or a user override; the `StxNamespace`
    // fixture's `probeNamed` probe pins this). M3b3 Task 3
    // (oracle-confirmed, `StxLocal.lean`): `local` then wraps the
    // ALREADY-qualified name in `_private.0.` — `elabSyntax`'s own
    // `stxNodeKind := (← getCurrNamespace) ++ name; if .. local then
    // stxNodeKind := mkPrivateName .. stxNodeKind` (`Lean/Elab/
    // Syntax.lean:434-436`) runs this gate AFTER qualifying, uniformly
    // for both the explicit-name and derived-name branches — same
    // ordering `notation.rs`'s `build_spec` now applies (that module's
    // own `private_kind_name` doc comment has the full citation).
    let qualified = match explicit_name {
        Some(n) => qualify_kind_name(current_ns, &escape_name_component(&n)),
        None => qualify_kind_name(current_ns, &mangle_items(category, item_nodes, kinds)),
    };
    let kind_name = if is_local {
        private_kind_name(&qualified)
    } else {
        qualified
    };

    // ORACLE-PORT `elabSyntax`'s `precDefault` (`Lean/Elab/Syntax.lean`):
    // atom-like syntax (first AND last item literal `Syntax.atom`)
    // defaults `MAX_PREC`, otherwise `LEAD_PREC` — the identical split
    // `derive_notation` already implements for `notation`.
    let prec = explicit_prec.unwrap_or(if is_atom_like(item_nodes, kinds) {
        MAX_PREC
    } else {
        LEAD_PREC
    });

    let body = Prim::Seq(body_prims);
    let mut tokens = Vec::new();
    walk_symbols(&body, &mut |s| tokens.push(s.to_string()));

    Some(GrammarDelta::Production(NotationSpec {
        category: category.to_string(),
        kind_name,
        leading,
        prec,
        lhs_prec,
        tokens,
        body,
        scope,
    }))
}

/// The `stx` category's own item grammar (`Lean/Parser/Syntax.lean`'s
/// `Syntax` namespace + the Init-bootstrapped quantifier-suffix trio),
/// walked to its runtime `Prim` — ORACLE-PORT of `Term.toParserDescr`'s
/// `process` (module doc). One arm per kind `command_syntax.rs`'s own
/// module doc pins against the `StxShapes` dump (11 productions); no
/// speculative arms — anything else (e.g. `Syntax.unicodeAtom`,
/// unexercised by any fixture, same "don't fabricate unexercised
/// productions" discipline `command_syntax.rs` already states) is
/// skip-and-record: `None` here kills the WHOLE enclosing command's
/// derivation (`build_from_items`'s `?`-propagated `.collect::<Option<_>>()`).
fn stx_item(node: &SyntaxNode, kinds: &KindInterner) -> Option<Prim> {
    match kinds.name(node.kind()) {
        "Lean.Parser.Syntax.atom" => {
            let str_node = node.children().next()?;
            if kinds.name(str_node.kind()) != "str" {
                return None;
            }
            let raw = first_token_text(&str_node)?;
            Some(Prim::Symbol(trim_lean_symbol(strip_quotes(&raw))))
        }
        "Lean.Parser.Syntax.nonReserved" => {
            let str_node = node.children().next()?;
            if kinds.name(str_node.kind()) != "str" {
                return None;
            }
            let raw = first_token_text(&str_node)?;
            Some(Prim::NonReservedSymbol(trim_lean_symbol(strip_quotes(
                &raw,
            ))))
        }
        // ORACLE-PORT `processNullaryOrCat` (`Lean/Elab/Syntax.lean`,
        // module doc's "critical divergence"): a bare ident item
        // resolves via `Parser.resolveParserName`'s priority — a real
        // CATEGORY name wins first, but `num`/`str`/`char`/`ident`/
        // `scientific` are never categories by default, so they fall
        // through to the builtin PARSER ALIAS table (`alias.rs`, "one
        // pinned table, two consumers") and resolve to a NULLARY alias
        // reference (`ParserDescr.const`) instead of a category
        // recursion. Since this pure walker has no environment to
        // query "is `name` a real category", it uses the alias table
        // as the disambiguator: a name the alias table resolves to a
        // CONST-arity mapping is never a realistic category name
        // (aliases are a small, fixed, reserved-word-shaped set —
        // nobody `declare_syntax_cat`s `num`), so alias-first,
        // category-fallback reproduces the oracle's real resolution
        // for every name this crate's fixtures (or realistic Mathlib
        // usage) can produce. An alias name resolving to a NON-const
        // arity (`Unary`/`Binary`/`Transparent` — a nullary reference
        // to a combinator that actually needs args, a genuine user
        // error the oracle itself rejects) is skip-and-record
        // (`None`), not silently coerced into a category guess.
        "Lean.Parser.Syntax.cat" => {
            let (name, rbp) = syntax_cat_name_and_rbp(node, kinds)?;
            match alias::lookup(&name) {
                Some(AliasPrim::Const(p)) => Some(p),
                Some(AliasPrim::Epsilon) => Some(Prim::Seq(vec![])),
                Some(_) => None,
                None => Some(Prim::Category { name, rbp }),
            }
        }
        "Lean.Parser.Syntax.unary" => {
            let fn_name = first_ident_token_text(node)?;
            let items_wrapper = node.children().next()?;
            let inner = stx_items_seq(&items_wrapper, kinds)?;
            match alias::lookup(&fn_name)? {
                AliasPrim::Unary(f) => Some(f(inner)),
                AliasPrim::Transparent => Some(inner),
                _ => None,
            }
        }
        "Lean.Parser.Syntax.binary" => {
            let fn_name = first_ident_token_text(node)?;
            let children: Vec<SyntaxNode> = node.children().collect();
            let a = stx_items_seq(children.first()?, kinds)?;
            let b = stx_items_seq(children.get(1)?, kinds)?;
            match alias::lookup(&fn_name)? {
                AliasPrim::Binary(f) => Some(f(a, b)),
                _ => None,
            }
        }
        "Lean.Parser.Syntax.sepBy" | "Lean.Parser.Syntax.sepBy1" => {
            let is1 = kinds.name(node.kind()) == "Lean.Parser.Syntax.sepBy1";
            let children: Vec<SyntaxNode> = node.children().collect();
            let item_wrapper = children.first()?;
            let item = Arc::new(stx_items_seq(item_wrapper, kinds)?);
            let str_node = children.get(1)?;
            if kinds.name(str_node.kind()) != "str" {
                return None;
            }
            let sep = trim_lean_symbol(strip_quotes(&first_token_text(str_node)?));
            // Children are `[items, str(sep), optional psep, optional
            // allowTrailingSep]`; the psep null-wrapper is always present
            // but empty for the plain `sepBy(p, ",")` form. A populated
            // custom psep (`sepBy(p, ", ", ", " p)`) is an unhandled
            // combinator — skip-and-record (never guess), so derive
            // nothing rather than dropping it into a wrong `Prim::SepBy`.
            if children.get(2)?.children_with_tokens().next().is_some() {
                return None;
            }
            let allow_wrapper = children.get(3)?;
            let allow_trailing = allow_wrapper.children_with_tokens().next().is_some();
            Some(if is1 {
                Prim::SepBy1 {
                    item,
                    sep,
                    allow_trailing,
                }
            } else {
                Prim::SepBy {
                    item,
                    sep,
                    allow_trailing,
                }
            })
        }
        "Lean.Parser.Syntax.paren" => {
            let items_wrapper = node.children().next()?;
            stx_items_seq(&items_wrapper, kinds)
        }
        // Init-bootstrapped quantifier-suffix trio (`command_syntax.rs`'s
        // module doc — the actual kind names the `StxShapes` dump
        // pins, guillemets transcribed verbatim): each wraps EXACTLY
        // the already-parsed lhs item as its sole node child (the
        // Pratt trailing-wrap mechanism, `Prim::TrailingNode`'s own doc
        // comment in `grammar/mod.rs`) — recurse into it, then apply
        // the postfix's own combinator (`p+` = `many1(p)`, `p?` =
        // `optional(p)`, `p,*` = `sepBy(p, ",")`, matching
        // `Init/Notation.lean`'s own bootstrapping macros).
        "«stx_+»" => {
            let inner_node = node.children().next()?;
            let inner = stx_item(&inner_node, kinds)?;
            Some(Prim::Many1(Arc::new(inner)))
        }
        "stx_?" => {
            let inner_node = node.children().next()?;
            let inner = stx_item(&inner_node, kinds)?;
            Some(Prim::Optional(Arc::new(inner)))
        }
        "«stx_,*»" => {
            let inner_node = node.children().next()?;
            let inner = stx_item(&inner_node, kinds)?;
            Some(Prim::SepBy {
                item: Arc::new(inner),
                sep: ",".to_string(),
                allow_trailing: false,
            })
        }
        _ => None,
    }
}

/// Walk EVERY node child of `wrapper` (a `many1(stx)`-produced `null`
/// node) via `stx_item`, folding into one `Prim` — `Prim::Seq` when
/// more than one item, the bare item itself when exactly one (mirrors
/// `NotationSpec::body`'s own "no gratuitous single-element Seq wrap"
/// shape, `notation.rs::build_spec`). `None` (skip-and-record) if the
/// wrapper is empty (a real oracle `many1` is never empty) or ANY
/// contained item is itself unrecognized.
fn stx_items_seq(wrapper: &SyntaxNode, kinds: &KindInterner) -> Option<Prim> {
    let mut items: Vec<Prim> = Vec::new();
    for child in wrapper.children() {
        items.push(stx_item(&child, kinds)?);
    }
    match items.len() {
        0 => None,
        1 => Some(items.into_iter().next().unwrap()),
        _ => Some(Prim::Seq(items)),
    }
}

/// `Syntax.cat := ident >> optPrecedence` — read both the category
/// ident and its optional `:prec` (defaulting `0`, ORACLE-PORT
/// `processParserCategory`'s `prec?.getD 0`) in one call, shared by
/// `stx_item`'s own `Syntax.cat` arm and `build_from_items`'s
/// `checkLeftRec` peek (both need the identical pair).
fn syntax_cat_name_and_rbp(node: &SyntaxNode, kinds: &KindInterner) -> Option<(String, u32)> {
    let name = first_ident_token_text(node)?;
    let prec_wrapper = node.children().next()?;
    let rbp = find_child(&prec_wrapper, "Lean.Parser.precedence", kinds)
        .and_then(|pn| read_prec_num(&pn, kinds))
        .unwrap_or(0);
    Some((name, rbp))
}

/// ORACLE-PORT `isAtomLikeSyntax` (`Lean/Elab/Syntax.lean`, pin
/// v4.32.0-rc1): first AND last top-level item are both literal
/// `Lean.Parser.Syntax.atom` nodes. Known gap: this port does NOT
/// implement the oracle's `paren`/`choice` transparency (`isAtomLikeSyntax
/// stx[1]` when `stx` is itself a `Syntax.paren`) — no fixture in this
/// corpus forces it; recorded, not silently wrong: a `syntax (foo)? :
/// cat`-shaped declaration whose first/last item is a bare `paren`
/// wrapping an atom would fall back to `LEAD_PREC` here where real Lean
/// would still call it atom-like.
fn is_atom_like(item_nodes: &[SyntaxNode], kinds: &KindInterner) -> bool {
    let is_atom = |n: &SyntaxNode| kinds.name(n.kind()) == "Lean.Parser.Syntax.atom";
    match (item_nodes.first(), item_nodes.last()) {
        (Some(f), Some(l)) => is_atom(f) && is_atom(l),
        _ => false,
    }
}

/// ORACLE-PORT `mkNameFromParserSyntax`'s `visit` (`Lean/Elab/
/// Syntax.lean`, pin v4.32.0-rc1) — read directly off the pinned
/// toolchain's own source (module doc), NOT the task brief's flat
/// `NotationAtom`-shaped sketch: a `str`-shaped node (only ever
/// `Lean.Parser.Syntax.atom`'s or `.nonReserved`'s wrapped child)
/// capitalizes its trimmed text (`mangle_symbol_atom`, the SAME
/// per-atom rule `notation`/`mixfix` already use); a
/// `Lean.Parser.Syntax.cat` node ALWAYS contributes a literal `_`,
/// REGARDLESS of its own ident text or precedence — even a bare `num :
/// widgetish` mangles to `widgetish_`, confirmed byte-exact against
/// `StxDeclareUse.stx.jsonl`'s own oracle dump (the `#check grab[42]`
/// line's antiquot-target kind is `widgetish_`); every OTHER node kind
/// (`.unary`/`.binary`/`.sepBy`/`.paren`/the postfix-suffix trio, or an
/// outer `null` items-wrapper) is mangle-TRANSPARENT — it recurses into
/// ALL of its own direct children (a leaf TOKEN, whether an `ident` or
/// a raw keyword `atom`, contributes nothing — matches the oracle's
/// `Syntax.ident ..`/`Syntax.atom ..` no-op arms in `visit`'s own
/// match). Confirmed byte-exact against `StxDeclareUse.stx.jsonl`'s
/// `«termGrab[_]»` kind for `"grab[" widgetish "]"` too (`"Grab["` +
/// `"_"` + `"]"`, guillemet-escaped since `[`/`]` aren't valid ident
/// characters). Omits the oracle's `Syntax.unicodeAtom` special case —
/// unreachable here: `stx_item`'s own dispatch never produces one
/// (skip-and-record, its own doc comment), so no tree reaching this
/// walk can contain that node kind.
fn mangle_visit(node: &SyntaxNode, kinds: &KindInterner, out: &mut String) {
    let name = kinds.name(node.kind());
    if name == "str" {
        if let Some(raw) = first_token_text(node) {
            out.push_str(&mangle_symbol_atom(strip_quotes(&raw)));
        }
        return;
    }
    if name == "Lean.Parser.Syntax.cat" {
        out.push('_');
        return;
    }
    for child in node.children() {
        mangle_visit(&child, kinds, out);
    }
}

/// `mkNameFromParserSyntax`'s outer shape: `appendCatName (visit
/// syntaxParser "")` then `Name.mkSimple` + escape
/// (`elabSyntax`/`elabMacro`'s own `mkUnusedBaseName` collision-
/// suffixing is out of scope, same "Deliberately out of scope"
/// carve-out `notation.rs`'s own module doc states for
/// `notation`/`mixfix`). `category` is prepended UNESCAPED
/// (`appendCatName`'s own `s ++ str` — `category` is always an
/// already-lexed plain ident, never itself needing escaping), then the
/// WHOLE joined string is escaped once (`escape_name_component`),
/// matching `mangle_kind`'s identical two-step shape.
fn mangle_items(category: &str, item_nodes: &[SyntaxNode], kinds: &KindInterner) -> String {
    let mut base = String::from(category);
    for n in item_nodes {
        mangle_visit(n, kinds, &mut base);
    }
    escape_name_component(&base)
}

/// The LAST direct-child TOKEN of `node` whose kind is `KIND_IDENT` —
/// the mirror image of `notation.rs`'s `first_ident_token_text`: a
/// `syntax`/`macroTail` node's own target-category ident is the FINAL
/// token, not the first. Scanning direct children only (never
/// descending into a NODE child) is unambiguous: `syntax`'s own body
/// can itself contain arbitrarily many `ident` tokens nested inside its
/// stx items, but those all live inside the items-wrapper NODE child,
/// never as a direct token child of the outer `syntax`/`macroTail`
/// node itself.
fn last_ident_token_text(node: &SyntaxNode) -> Option<String> {
    // `rowan::SyntaxElementChildren` isn't `DoubleEndedIterator` — collect
    // then scan back-to-front (this crate's direct-child lists are all
    // small, a handful of tokens/nodes, never user-scale data).
    let elements: Vec<_> = node.children_with_tokens().collect();
    elements.into_iter().rev().find_map(|el| {
        let t = el.into_token()?;
        (t.kind() == KIND_IDENT).then(|| t.text().to_string())
    })
}

/// `namedName`'s own `(name := $ident)` override, if the optional slot
/// (`children.get(attr_kind_pos+2)`, this module's callers) is
/// populated — `find_child` finds the wrapped `Lean.Parser.Command.
/// namedName` node (`StxShapes.stx.jsonl`: `Command.namedName{"(",
/// "name", ":=", ident"probed", ")"}`, all-token children), then scans
/// ITS direct tokens for the ident (same `KIND_IDENT`-by-kind approach
/// as `first_ident_token_text`, reused directly since `namedName`'s
/// ident is unambiguously the ONLY ident among its 5 token children).
fn named_name_ident(wrapper: &SyntaxNode, kinds: &KindInterner) -> Option<String> {
    let nn = find_child(wrapper, "Lean.Parser.Command.namedName", kinds)?;
    first_ident_token_text(&nn)
}
