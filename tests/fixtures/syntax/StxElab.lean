-- M3b3 Task 10: `elab`/`binderPredicate` grammar-side derivation — the
-- rejoin to `GRAMMAR_GROWING_KINDS` (M3b2b's PR #13 dropped both names
-- pending this task, `surface.rs`'s own `derive_surface` doc comment).
--
-- `derive_elab_cmd` mirrors `derive_macro_cmd` byte-for-byte
-- (`Lean/Parser/Syntax.lean:125-129`: `elabArg := macroArg`, and
-- `elabTail := leading_parser atomic (" : " >> ident >> optional (" <= "
-- >> ident)) >> darrow >> withPosition termParser` — the SAME
-- `[null(doc), null(attrs), attrKind, null(prec?), null(namedName?),
-- null(namedPrio?), null(many1 elabArg), <tail node>]` 8-child layout
-- `macro` has) — only the tail node's own kind name differs
-- (`Lean.Parser.Command.elabTail` vs `..macroTail`) and the target
-- category ident is read the identical way (`last_ident_token_text`
-- on the tail node: `elabTail`'s own optional `<= expectedType`
-- binder is nested one level inside its OWN null wrapper, invisible to
-- a direct `children_with_tokens()` scan, so it can never shadow the
-- real category ident — same reasoning already applies to `macroTail`,
-- which has no such trailing optional at all). `local elab`/`scoped
-- elab` are real Mathlib patterns (`Mathlib/Tactic/Contrapose.lean`,
-- `Mathlib/Geometry/Manifold/Notation.lean`) — `local elab` below pins
-- that `derive_elab_cmd` reuses the SAME `spec_scope_from_attr_kind`
-- gate `derive_macro_cmd` already does, unmodified.
--
-- `derive_binder_predicate` targets the oracle's own `binderPred`
-- category (`Init/BinderPredicates.lean:22`'s `declare_syntax_cat
-- binderPred` — confirmed from source, not guessed, exactly like the
-- brief asked). Its own attrKind slot is DOUBLE-wrapped
-- (`Lean/Parser/Syntax.lean:137-139`'s `optional Term.attrKind`, not
-- `syntax`/`macro`/`elab`'s bare `Term.attrKind`) because `Term.attrKind`
-- itself already always succeeds (`Lean/Parser/Term.lean:586`'s own
-- `optional (scoped <|> local)`) — the outer `optional` around an
-- always-succeeding parser always takes the "matched" branch, so the
-- wrapper is never truly empty, but it IS an extra indirection layer a
-- direct kind-name child search would miss; `derive_binder_predicate`
-- locates it via a nested `find_child` instead. `binder_predicate`'s
-- registered production is the `args` tail ONLY (the leading bound
-- `ident` — `wbx` below — is never part of the registered `binderPred`
-- syntax itself, per `Lean/Elab/BinderPredicates.lean`'s own
-- `elabBinderPred`: it is consumed separately by the `macro_rules`
-- companion registration, out of this task's grammar-only remit).
elab "wobel" : term => pure (Lean.mkNatLit 42)
#check wobel
local elab "wobello" : term => pure (Lean.mkNatLit 43)
#check wobello
binder_predicate wbx " wobrel " wby:term => `(f $wbx $wby)
