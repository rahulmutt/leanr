//! Interprets a `ParserDescr` constant's term-bank value into a `Prim`.
//! ORACLE-PORT of `compileParserDescr`/`mkParserOfConstant`
//! (Lean/Parser/Extension.lean:255-304): structural walk only — no
//! evaluator. Anything that is not a literal constructor tree
//! skips-and-records (M3b2a spec §Error handling).

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId, Store};
use leanr_kernel::ConstantInfo;
use leanr_syntax::grammar::notation::{escape_name_component, trim_lean_symbol};
use leanr_syntax::grammar::Prim;
use leanr_syntax::grammar::SnapshotBuilder;

use crate::alias::{self, AliasPrim};
use crate::SkipReason;

#[derive(Debug)]
pub(crate) enum Interpreted {
    Leading(Prim),
    Trailing(Prim),
}

struct Cx<'a> {
    store: &'a Store,
    consts: &'a HashMap<NameId, &'a ConstantInfo>,
    builder: &'a mut SnapshotBuilder,
    visiting: HashSet<NameId>,
}

pub(crate) fn interpret(
    decl: NameId,
    consts: &HashMap<NameId, &ConstantInfo>,
    store: &Store,
    builder: &mut SnapshotBuilder,
) -> Result<Interpreted, SkipReason> {
    let mut cx = Cx {
        store,
        consts,
        builder,
        visiting: HashSet::new(),
    };
    cx.decl(decl)
}

/// Lean symbol strings carry pretty-print padding — `" ⊕⊕ "`; the token
/// is the trimmed core. Reuses `leanr_syntax`'s `trim_lean_symbol`
/// (Lean-whitespace-only trim, matching `mangle_symbol_atom`).
fn trim_symbol(s: &str) -> String {
    trim_lean_symbol(s)
}

/// Strip the `Lean.` namespace prefix that fully-qualified constructor
/// names carry in decoded `.olean` values, so dispatch keys stay short
/// and stable (`Lean.ParserDescr.symbol` → `ParserDescr.symbol`).
fn strip_lean(name: &str) -> &str {
    name.strip_prefix("Lean.").unwrap_or(name)
}

impl Cx<'_> {
    /// Leading/trailing from the constant's declared TYPE
    /// (mkParserOfConstant): ParserDescr → leading,
    /// TrailingParserDescr → trailing, Parser/TrailingParser → raw skip.
    fn decl(&mut self, decl: NameId) -> Result<Interpreted, SkipReason> {
        let info = *self.consts.get(&decl).ok_or(SkipReason::MissingConstant)?;
        let ty = self.const_head_name(info.constant_val().ty);
        let value = match info {
            ConstantInfo::Defn(d) => d.value,
            _ => return Err(SkipReason::UnsupportedShape("non-def parser constant")),
        };
        match ty.as_deref().map(strip_lean) {
            Some("ParserDescr") => Ok(Interpreted::Leading(self.descr(value)?)),
            Some("TrailingParserDescr") => Ok(Interpreted::Trailing(self.descr(value)?)),
            Some("Parser.Parser") | Some("Parser.TrailingParser") => Err(SkipReason::RawParser),
            _ => Err(SkipReason::UnsupportedShape(
                "unexpected parser constant type",
            )),
        }
    }

    /// The 13-constructor walk (tags per Init/Prelude.lean:5363-5449;
    /// dispatch is by CONSTRUCTOR NAME on the app-spine head, which is
    /// stable across tag renumbering).
    fn descr(&mut self, e: ExprId) -> Result<Prim, SkipReason> {
        let (head, args) = self.app_spine(e);
        let Some(head) = head else {
            return Err(SkipReason::UnsupportedShape("descr head is not a const"));
        };
        let full = self.name_string(head);
        let name = strip_lean(&full);
        match (name, args.len()) {
            ("ParserDescr.const", 1) => {
                let alias = self.eval_name(args[0])?;
                match alias::lookup(&alias) {
                    Some(AliasPrim::Const(p)) => Ok(p),
                    Some(AliasPrim::Epsilon) => Ok(Prim::Seq(vec![])),
                    Some(_) => Err(SkipReason::UnsupportedShape("alias arity mismatch")),
                    None => Err(SkipReason::UnknownAlias(alias)),
                }
            }
            ("ParserDescr.unary", 2) => {
                let alias = self.eval_name(args[0])?;
                let inner = self.descr(args[1])?;
                match alias::lookup(&alias) {
                    Some(AliasPrim::Unary(f)) => Ok(f(inner)),
                    Some(AliasPrim::Transparent) => Ok(inner),
                    Some(_) => Err(SkipReason::UnsupportedShape("alias arity mismatch")),
                    None => Err(SkipReason::UnknownAlias(alias)),
                }
            }
            ("ParserDescr.binary", 3) => {
                let alias = self.eval_name(args[0])?;
                let (a, b) = (self.descr(args[1])?, self.descr(args[2])?);
                match alias::lookup(&alias) {
                    Some(AliasPrim::Binary(f)) => Ok(f(a, b)),
                    Some(_) => Err(SkipReason::UnsupportedShape("alias arity mismatch")),
                    None => Err(SkipReason::UnknownAlias(alias)),
                }
            }
            ("ParserDescr.node", 3) => {
                let kind = self.intern_kind(args[0])?;
                let prec = self.eval_prec(args[1])?;
                Ok(Prim::Node {
                    kind,
                    prec: Some(prec),
                    body: Arc::new(self.descr(args[2])?),
                })
            }
            ("ParserDescr.trailingNode", 4) => {
                let kind = self.intern_kind(args[0])?;
                let prec = self.eval_prec(args[1])?;
                let lhs_prec = self.eval_prec(args[2])?;
                Ok(Prim::TrailingNode {
                    kind,
                    prec,
                    lhs_prec,
                    body: Arc::new(self.descr(args[3])?),
                })
            }
            ("ParserDescr.symbol", 1) => Ok(Prim::Symbol(trim_symbol(&self.eval_string(args[0])?))),
            ("ParserDescr.nonReservedSymbol", 2) => Ok(Prim::NonReservedSymbol(trim_symbol(
                &self.eval_string(args[0])?,
            ))),
            ("ParserDescr.cat", 2) => Ok(Prim::Category {
                name: self.eval_name(args[0])?,
                rbp: self.eval_prec(args[1])?,
            }),
            ("ParserDescr.parser", 1) => {
                // Reference to another parser decl: recurse (cycle-guarded).
                let target = self.eval_name_id(args[0])?;
                if !self.visiting.insert(target) {
                    return Err(SkipReason::Cycle);
                }
                let r = self.decl(target);
                self.visiting.remove(&target);
                match r? {
                    Interpreted::Leading(p) | Interpreted::Trailing(p) => Ok(p),
                }
            }
            ("ParserDescr.nodeWithAntiquot", 3) => {
                // Antiquot behavior itself is M3b2b; the real-source path
                // is the plain node (compileParserDescr wraps only for
                // quotation contexts).
                let kind = self.intern_kind(args[1])?;
                Ok(Prim::Node {
                    kind,
                    prec: None,
                    body: Arc::new(self.descr(args[2])?),
                })
            }
            ("ParserDescr.sepBy", 4) | ("ParserDescr.sepBy1", 4) => {
                let item = Arc::new(self.descr(args[0])?);
                let sep = trim_symbol(&self.eval_string(args[1])?);
                // args[2] is psep (the separator PARSER — usually
                // `symbol sep`); leanr's SepBy carries the separator
                // token directly, matching the builtin ports.
                let allow_trailing = self.eval_bool(args[3])?;
                Ok(if name.ends_with('1') {
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
            ("ParserDescr.unicodeSymbol", 3) => {
                // Parses either form; tokens for both are harvested.
                let uni = trim_symbol(&self.eval_string(args[0])?);
                let ascii = trim_symbol(&self.eval_string(args[1])?);
                Ok(Prim::OrElse(vec![Prim::Symbol(uni), Prim::Symbol(ascii)]))
            }
            _ => Err(SkipReason::UnsupportedShape(
                "unknown ParserDescr constructor",
            )),
        }
    }

    /// Uncurry an application spine: `App(App(Const c, a), b)` → (c, [a, b]).
    /// Walks through `Mdata` transparently. Returns head const NameId.
    fn app_spine(&self, e: ExprId) -> (Option<NameId>, Vec<ExprId>) {
        let mut args: Vec<ExprId> = Vec::new();
        let mut cur = e;
        loop {
            match self.store.expr_node(None, cur) {
                Node::App { f, arg } => {
                    args.push(arg);
                    cur = f;
                }
                Node::MData { expr, .. } => cur = expr,
                Node::Const { name, .. } => {
                    args.reverse();
                    return (name, args);
                }
                _ => return (None, Vec::new()),
            }
        }
    }

    /// The head const name of an expr (its declared TYPE, for `decl`),
    /// unwrapping `Mdata`. `None` if the head is not a `Const`.
    fn const_head_name(&self, e: ExprId) -> Option<String> {
        let (head, _) = self.app_spine(e);
        head.map(|n| self.name_string(n))
    }

    fn name_string(&self, n: NameId) -> String {
        self.store.to_name(None, Some(n)).to_string()
    }

    /// Evaluate a `Name`-typed literal expr into its dotted string form.
    /// Observed encodings in NotaDep.olean (see oracle comment on
    /// `push_name_parts`): `Name.mkStr*` helper apps and `Name.str`
    /// ctor chains rooted at `Name.anonymous`.
    fn eval_name(&self, e: ExprId) -> Result<String, SkipReason> {
        let mut parts: Vec<String> = Vec::new();
        self.push_name_parts(e, &mut parts)?;
        Ok(parts.join("."))
    }

    /// Resolve a `Name` literal to a `NameId` that is a KEY of `consts`
    /// (the closure's constant map). Used only by `ParserDescr.parser`
    /// references, which must point at a constant present in the closure.
    /// Resolution is by reconstructed dotted string (the store is
    /// immutable here, so we cannot re-intern; matching against existing
    /// keys returns the exact interned id `decl`/`visiting` need).
    fn eval_name_id(&self, e: ExprId) -> Result<NameId, SkipReason> {
        let want = self.eval_name(e)?;
        self.consts
            .keys()
            .copied()
            .find(|k| self.name_string(*k) == want)
            .ok_or(SkipReason::MissingConstant)
    }

    /// Push the components of a `Name` literal onto `parts` (root-first).
    /// ORACLE observed shapes (NotaDep.olean, dumped via the `dump_shapes`
    /// scratch test):
    ///   - `Name.anonymous` (Const, 0 args)            → no parts
    ///   - `Name.str parent (strlit)` (App, 2 args)    → parts(parent) ++ [s]
    ///   - `Name.num parent (natlit)` (App, 2 args)    → parts(parent) ++ [n]
    ///   - `Name.mkStr1..mkStr8 s1 .. sN` (App, N args)→ [s1, .., sN]
    ///     (anonymous-rooted string chain; the elaborator emits these for
    ///     name literals up to 8 components — Init/Prelude.lean)
    ///   - `Name.mkSimple s` (App, 1 arg)              → [s]
    ///
    /// Anything else → UnsupportedShape("name literal").
    fn push_name_parts(&self, e: ExprId, parts: &mut Vec<String>) -> Result<(), SkipReason> {
        let (head, args) = self.app_spine(e);
        let Some(head) = head else {
            return Err(SkipReason::UnsupportedShape(
                "name literal head is not a const",
            ));
        };
        let full = self.name_string(head);
        let name = strip_lean(&full);
        match (name, args.len()) {
            ("Name.anonymous", 0) => Ok(()),
            ("Name.str", 2) => {
                self.push_name_parts(args[0], parts)?;
                parts.push(self.eval_string(args[1])?);
                Ok(())
            }
            ("Name.num", 2) => {
                self.push_name_parts(args[0], parts)?;
                parts.push(self.eval_nat(args[1])?.to_string());
                Ok(())
            }
            ("Name.mkSimple", 1) => {
                parts.push(self.eval_string(args[0])?);
                Ok(())
            }
            (n, k) if n.starts_with("Name.mkStr") && k >= 1 => {
                // mkStr1..mkStr8: all args are string leaves, anon-rooted.
                for &a in &args {
                    parts.push(self.eval_string(a)?);
                }
                Ok(())
            }
            (n, k) if n.starts_with("Name.mkNum") && k == 2 => {
                self.push_name_parts(args[0], parts)?;
                parts.push(self.eval_nat(args[1])?.to_string());
                Ok(())
            }
            _ => Err(SkipReason::UnsupportedShape("name literal")),
        }
    }

    /// String literal leaf: `Node::LitStr` → interned pool string.
    /// Anything else → UnsupportedShape("string literal").
    fn eval_string(&self, e: ExprId) -> Result<String, SkipReason> {
        // Unwrap Mdata transparently (elaborator may annotate literals).
        let mut cur = e;
        loop {
            match self.store.expr_node(None, cur) {
                Node::LitStr { v } => return Ok(self.store.str_at(None, v).to_string()),
                Node::MData { expr, .. } => cur = expr,
                _ => return Err(SkipReason::UnsupportedShape("string literal")),
            }
        }
    }

    /// Evaluate a `Nat` literal to a `u64` (skip if it does not fit).
    /// Observed encodings (see `eval_prec` oracle comment):
    ///   - `Node::LitNat`                          (bare kernel Nat literal)
    ///   - `@OfNat.ofNat Nat n (instOfNatNat n)`   (elaborated numeral)
    ///     head `OfNat.ofNat`, 3 args, args[1] is the `LitNat`.
    fn eval_nat(&self, e: ExprId) -> Result<u64, SkipReason> {
        let mut cur = e;
        loop {
            match self.store.expr_node(None, cur) {
                Node::LitNat { v } => {
                    let n = self.store.nat_at(None, v);
                    return n
                        .to_usize()
                        .map(|u| u as u64)
                        .ok_or(SkipReason::UnsupportedShape("nat literal too large"));
                }
                Node::MData { expr, .. } => cur = expr,
                Node::App { .. } | Node::Const { .. } => {
                    let (head, args) = self.app_spine(cur);
                    let name = head.map(|h| self.name_string(h));
                    match name.as_deref().map(strip_lean) {
                        Some("OfNat.ofNat") if args.len() == 3 => {
                            cur = args[1];
                        }
                        _ => return Err(SkipReason::UnsupportedShape("nat literal")),
                    }
                }
                _ => return Err(SkipReason::UnsupportedShape("nat literal")),
            }
        }
    }

    /// Precedence/rbp: a `Nat` literal narrowed to `u32` (precs never
    /// exceed `u32::MAX`; skip if they somehow do).
    fn eval_prec(&self, e: ExprId) -> Result<u32, SkipReason> {
        let n = self.eval_nat(e)?;
        u32::try_from(n).map_err(|_| SkipReason::UnsupportedShape("prec exceeds u32"))
    }

    /// `Bool.true` / `Bool.false` const leaves.
    fn eval_bool(&self, e: ExprId) -> Result<bool, SkipReason> {
        let (head, args) = self.app_spine(e);
        let Some(head) = head else {
            return Err(SkipReason::UnsupportedShape("bool literal"));
        };
        if !args.is_empty() {
            return Err(SkipReason::UnsupportedShape("bool literal"));
        }
        match strip_lean(&self.name_string(head)) {
            "Bool.true" => Ok(true),
            "Bool.false" => Ok(false),
            _ => Err(SkipReason::UnsupportedShape("bool literal")),
        }
    }

    /// Evaluate a `Name`-typed literal expr into its ESCAPED display-string
    /// form — the string a real Lean `kind.toString()` prints, e.g.
    /// `«term_⊕⊕_»` for the mangled component `term_⊕⊕_`. Both the oracle
    /// dumps (`ImportMixfix.stx.jsonl`'s `"k"` fields) and M3b1's native
    /// path (`notation::mangle_kind`, which calls `escape_name_component`)
    /// use this escaped form, never the raw joined `Name`.
    ///
    /// Lean's `Name.toString` escapes each `.`-separated component
    /// INDEPENDENTLY (`escapePart`/`needsNoEscape`) and joins with `.`,
    /// not one `escape_name_component` call over the whole joined string
    /// (same distinction `notation.rs::mangle_private_kind` documents,
    /// e.g. a scoped kind `NotaDep.term_⊖⊖_` escapes as `NotaDep.«term_⊖⊖_»`
    /// — `NotaDep` is already a valid identifier so `needs_no_escape`
    /// leaves it bare, only the mangled-symbol component needs guillemets).
    ///
    /// CRITICAL: used ONLY by `intern_kind`. `eval_name` (raw, unescaped)
    /// remains the only `Name`-evaluator for alias lookup keys
    /// (`"andthen"`), category names (`"term"`/`"widget"`, matched
    /// against the category table's plain-identifier keys), and
    /// `ParserDescr.parser` target resolution (matched against kernel
    /// `Display`, which is raw) — escaping those would break the lookups.
    fn eval_name_display(&self, e: ExprId) -> Result<String, SkipReason> {
        let mut parts: Vec<String> = Vec::new();
        self.push_name_parts(e, &mut parts)?;
        Ok(parts
            .iter()
            .map(|p| escape_name_component(p))
            .collect::<Vec<_>>()
            .join("."))
    }

    /// Kind names intern via the builder (single interner for the whole
    /// assembled snapshot), under the ESCAPED display form (see
    /// `eval_name_display`) — matching the oracle dump's guillemet
    /// quoting, e.g. `«term_⊕⊕_»`, not the raw mangled name.
    fn intern_kind(&mut self, e: ExprId) -> Result<leanr_syntax::kind::SyntaxKind, SkipReason> {
        let name = self.eval_name_display(e)?;
        Ok(self.builder.kind(&name))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use std::path::Path;

    use leanr_kernel::bank::Store;
    use leanr_olean::{EntryScope, ModuleData, ParserEntry};
    use leanr_syntax::grammar::Prim;

    fn load_notadep() -> (Store, ModuleData) {
        let p = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures/syntax/import/NotaDep.olean");
        let mut st = Store::persistent();
        let md = ModuleData::parse(&std::fs::read(p).unwrap(), &mut st).unwrap();
        (st, md)
    }

    /// Returns the interpreted result AND the finished snapshot, so a
    /// golden can resolve an interned `SyntaxKind` back to the exact
    /// string `intern_kind` handed the builder (M3b2a Task 6 review
    /// Finding 2: pin the escaped kind name, not just its shape).
    fn interpret_named(
        suffix: &str,
    ) -> (
        Result<Interpreted, crate::SkipReason>,
        leanr_syntax::grammar::GrammarSnapshot,
    ) {
        let (st, md) = load_notadep();
        let consts: HashMap<_, _> = md
            .constants
            .iter()
            .map(|c| (c.constant_val().name, c))
            .collect();
        let decl = md
            .parser_entries
            .iter()
            .find_map(|e| match (&e.scope, &e.entry) {
                (EntryScope::Global, ParserEntry::Parser { decl, .. })
                    if st.to_name(None, Some(*decl)).to_string().ends_with(suffix) =>
                {
                    Some(*decl)
                }
                _ => None,
            })
            .unwrap_or_else(|| panic!("no parser entry ending {suffix}"));
        let mut b = leanr_syntax::builtin::builder();
        let r = interpret(decl, &consts, &st, &mut b);
        (r, b.finish())
    }

    #[test]
    fn infixl_interprets_as_trailing_node() {
        // infixl:65 " ⊕⊕ " ⇒ TrailingParserDescr =
        //   trailingNode `«term_⊕⊕_» 65 65 (symbol " ⊕⊕ " >> cat term 66)
        // (rbp 66 = p+1 for left-assoc; kind name is Lean's mangling —
        //  both already pinned by ImportMixfix.stx.jsonl.)
        //
        // NOTE (Task 3 decode): the parser-entry `decl` name is the
        // UNMANGLED constant name `term_⊕⊕_`, not the mangled kind
        // `«term_⊕⊕_»` (which is what `trailingNode`'s kind arg holds).
        let (r, snap) = interpret_named("term_⊕⊕_");
        let Interpreted::Trailing(p) = r.expect("interpreted") else {
            panic!("expected trailing")
        };
        let Prim::TrailingNode {
            kind,
            prec,
            lhs_prec,
            body,
        } = p
        else {
            panic!("expected TrailingNode, got {p:?}")
        };
        assert_eq!((prec, lhs_prec), (65, 65));
        // Review Finding 2: pin the INTERNED kind name to the escaped
        // display form — exactly the `"k"` field ImportMixfix.stx.jsonl's
        // ⊕⊕ line carries (`"k":"«term_⊕⊕_»"`), not the raw joined name
        // `term_⊕⊕_` that a pre-fix `intern_kind` would have used.
        assert_eq!(snap.kinds().name(kind), "«term_⊕⊕_»");
        let Prim::Seq(items) = &*body else {
            panic!("expected Seq, got {body:?}")
        };
        assert!(
            matches!(&items[0], Prim::Symbol(s) if s == "⊕⊕"),
            "first item {:?}",
            items[0]
        );
        assert!(
            matches!(&items[1], Prim::Category { name, rbp } if name == "term" && *rbp == 66),
            "second item {:?}",
            items[1]
        );
    }

    #[test]
    fn prefix_interprets_as_leading_node() {
        // prefix:100 "⋄⋄" ⇒ ImportMixfix.stx.jsonl's `#check ⋄⋄ 1` line
        // carries `"k":"«term⋄⋄_»"` for the generated kind.
        let (r, snap) = interpret_named("term⋄⋄_");
        let Interpreted::Leading(Prim::Node { kind, prec, .. }) = r.expect("interpreted") else {
            panic!("expected leading Node")
        };
        assert_eq!(prec, Some(100));
        assert_eq!(snap.kinds().name(kind), "«term⋄⋄_»");
    }

    #[test]
    fn category_reference_interprets() {
        // syntax "wrap[" widget "]" : term — body contains cat widget.
        let (r, _snap) = interpret_named("termWrap[_]");
        let Interpreted::Leading(prim) = r.unwrap_or_else(|e| panic!("skip: {e:?}")) else {
            panic!("expected leading")
        };
        let dbg = format!("{prim:?}");
        assert!(dbg.contains("widget"), "no widget category in {dbg}");
    }
}
