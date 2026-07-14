# M3a builtin-parser surface (pinned v4.32.0-rc1)

Generated from `scripts/builtin-surface.sh` on 2026-07-14; hand-annotated.
The M3a rule: a construct may appear in fixtures iff every parser it
touches is on this list with status `port` (or is machinery like
`ident`/literals). `Init/`-declared syntax (ParserDescr) is M3b.

**239** `@[builtin_*_parser]` declarations across 10 categories, spread
over 10 files. 236 live under `Lean/Parser/` (8 files: `Attr.lean`,
`Command.lean`, `Do.lean`, `Level.lean`, `Syntax.lean`, `Tactic.lean`,
`Term.lean`, `Term/Basic.lean` — `Lean/Parser/` has 17 `.lean` files
total, 9 of them with zero builtin-parser attributes); 3 live elsewhere
in the toolchain (`Lean/Elab/Term/TermElabM.lean`,
`Lean/Meta/Tactic/Grind/Parser.lean`) — see §Enumeration notes.

## Enumeration notes (read before trusting the table)

The naive `grep -rnoE '@\[builtin_[a-z_]+_parser...' "Lean/Parser"`
one-liner sketched in the task brief gives 202 rows — 1 short of even
being internally consistent, since one of those 202 (`depArrow`) is a
double-count of a single real declaration (the real one plus a
commented-out rejected design sharing the name). The true count is
**239**, for five distinct reasons the naive regex gets wrong, all fixed
in `scripts/builtin-surface.sh`:

1. **Category names aren't all lowercase.** `[a-z_]+` drops
   `builtin_doElem_parser` (27 hits — the entire do-element category)
   and `builtin_structInstFieldDecl_parser` (2 hits) outright.
2. **Attribute and `def` sometimes sit on different lines**
   (`@[builtin_term_parser]\ndef «forall» := ...`). A same-line-only
   regex silently drops these — including `«forall»` and `«letrec»`,
   not obscure constructs.
3. **Declared names are sometimes qualified**
   (`Term.quot`, `Tactic.quotSeq`). An identifier class without `.`
   truncates them to `Term` / `Tactic`, which then look like bogus
   duplicate declarations of a category-registration parser.
4. **The toolchain's own comments contain example
   `@[builtin_..._parser] def ...` lines as prose or disabled code**
   (a *separate*, additive bug from the two above) — six confirmed
   sites, none a live declaration: `Lean/Parser/Term.lean:250` (a
   rejected `depArrow` design, inside a `/- ... -/` block — double-
   counting the real `depArrow` at `Term.lean:256`), `Lean/Parser/
   Do.lean:118` (`doReassignElse`, behind a `--` line comment),
   `Lean/Attributes.lean:80-84` (a `/-! -/` module doc illustrating
   `Attr.lean`'s own `simple`/`«macro»`/`«export»` declarations),
   `Lean/Meta/RecursorInfo.lean:221` (a `/- -/`-commented-out
   `recursor`), `Lean/Elab/StructInst.lean:36-64` (a `/-! -/` module doc
   block containing `structInstFieldDef`/`structInstFieldEqns` examples
   that duplicate the real decls plus a `structInstFieldWhere` example —
   this name has **no live declaration anywhere** in the toolchain; it
   is aspirational text, not a parser), and
   `Lean/Compiler/ExternAttr.lean:44` (a `--`-commented-out `extern`
   attribute-parser, duplicating the real `extern` at `Attr.lean:53`).
   Plain grep counts all of these as hits; a real compiler wouldn't.
   Confirmed via a character-level scan tracking nested `/- -/` depth,
   `--` line comments, and `"..."` string literals (`\`-escaped) — the
   same class of bug a hand-rolled Lean tokenizer must get right anyway,
   so validating it here doubles as an early sanity check on that logic.
5. **The attribute is not confined to `Lean/Parser/`.** Scanning the
   pinned toolchain's whole `src/lean` tree (grep -l prefilter — only 14
   files match at all, so this costs nothing) finds three more genuine,
   live declarations: `Lean.Parser.Term.elabToSyntax`
   (`Lean/Elab/Term/TermElabM.lean:815`) and `grindPattern` /
   `initGrindNorm` (`Lean/Meta/Tactic/Grind/Parser.lean:140,143`, the
   `grind` tactic's pattern-registration commands). A `Lean/Parser/`-only
   scan would silently miss these three.

`scripts/builtin-surface.sh` scans the whole pinned `src/lean` tree with
a comment/string-aware character scanner and reproduces exactly 239
rows, cross-checked three independent ways: (a) raw `@[builtin_` count
(312) minus non-`_parser` attributes (`builtin_doc`: 74, `builtin_init
alize`: not attribute-shaped at all) equals 238 raw `_parser`-attribute
occurrences of which 2 are commented-out and 3 live outside
`Lean/Parser/`, netting 239; (b) per-category counts summed
(112+62+27+12+9+7+6+2+1+1 = 239); (c) manual line-by-line read of every
file that `grep -l` flagged (14 files) confirming no attribute site was
missed and no flagged site was a false positive.

## attr category (`Lean/Parser/Attr.lean`) — 12

| parser | kind name | source | M3a status |
|---|---|---|---|
| simple | Lean.Parser.Attr.simple | Attr.lean:39 | port |
| «macro» | Lean.Parser.Attr.«macro» | Attr.lean:41 | port (the `@[macro foo]` attribute value, distinct from the `macro` command) |
| «export» | Lean.Parser.Attr.«export» | Attr.lean:42 | port |
| recursor | Lean.Parser.Attr.recursor | Attr.lean:45 | port |
| «class» | Lean.Parser.Attr.«class» | Attr.lean:46 | port |
| «instance» | Lean.Parser.Attr.«instance» | Attr.lean:47 | port |
| default_instance | Lean.Parser.Attr.default_instance | Attr.lean:48 | port |
| «specialize» | Lean.Parser.Attr.«specialize» | Attr.lean:49 | port |
| extern | Lean.Parser.Attr.extern | Attr.lean:53 | port |
| «tactic_alt» | Lean.Parser.Attr.«tactic_alt» | Attr.lean:63 | port |
| «tactic_tag» | Lean.Parser.Attr.«tactic_tag» | Attr.lean:71 | port |
| «tactic_name» | Lean.Parser.Attr.«tactic_name» | Attr.lean:84 | port |

All 12 are trivial fixed-shape attribute-argument parsers (an ident, a
priority, a string, or nothing) — no ParserDescr, no macro expansion.
All port.

## command category (`Lean/Parser/Command.lean`, `Lean/Parser/Syntax.lean`, `Lean/Meta/Tactic/Grind/Parser.lean`) — 62

`Lean/Parser/Module.lean` has **zero** builtin-parser attributes (module
header commands like `import` parse via `Command.lean`'s `«import»` /
`importPath`) — the brief's placeholder table header mentioning
`Module.lean` doesn't apply; noted so Task 7 doesn't go looking there.

| parser | kind name | source | M3a status |
|---|---|---|---|
| moduleDoc | Lean.Parser.Command.moduleDoc | Command.lean:59 | port |
| declaration | Lean.Parser.Command.declaration | Command.lean:282 | port (the `def`/`theorem`/`instance`/… dispatcher — fixture-critical) |
| «deriving» | Lean.Parser.Command.«deriving» | Command.lean:286 | port (syntactic clause only; handler dispatch is elaboration, M4) |
| «section» | Lean.Parser.Command.«section» | Command.lean:299 | port |
| «namespace» | Lean.Parser.Command.«namespace» | Command.lean:317 | port |
| withWeakNamespace | Lean.Parser.Command.withWeakNamespace | Command.lean:330 | port |
| «end» | Lean.Parser.Command.«end» | Command.lean:337 | port |
| «variable» | Lean.Parser.Command.«variable» | Command.lean:471 | port |
| «universe» | Lean.Parser.Command.«universe» | Command.lean:531 | port |
| check | Lean.Parser.Command.check | Command.lean:533 | port |
| check_failure | Lean.Parser.Command.check_failure | Command.lean:535 | port |
| importPath | Lean.Parser.Command.importPath | Command.lean:541 | port |
| assertNotExists | Lean.Parser.Command.assertNotExists | Command.lean:547 | port |
| assertNotImported | Lean.Parser.Command.assertNotImported | Command.lean:553 | port |
| checkAssertions | Lean.Parser.Command.checkAssertions | Command.lean:560 | port |
| eval | Lean.Parser.Command.eval | Command.lean:586 | port |
| evalBang | Lean.Parser.Command.evalBang | Command.lean:588 | port |
| synth | Lean.Parser.Command.synth | Command.lean:590 | port |
| exit | Lean.Parser.Command.exit | Command.lean:592 | port (`#exit` — trivial, still port) |
| print | Lean.Parser.Command.print | Command.lean:594 | port |
| printSig | Lean.Parser.Command.printSig | Command.lean:596 | port |
| printAxioms | Lean.Parser.Command.printAxioms | Command.lean:600 | port |
| printEqns | Lean.Parser.Command.printEqns | Command.lean:602 | port |
| printTacTags | Lean.Parser.Command.printTacTags | Command.lean:607 | port |
| «where» | Lean.Parser.Command.«where» | Command.lean:614 | port |
| version | Lean.Parser.Command.version | Command.lean:617 | port |
| withExporting | Lean.Parser.Command.withExporting | Command.lean:623 | port |
| dumpAsyncEnvState | Lean.Parser.Command.dumpAsyncEnvState | Command.lean:626 | port |
| deprecatedSyntax | Lean.Parser.Command.deprecatedSyntax | Command.lean:635 | port |
| «init_quot» | Lean.Parser.Command.«init_quot» | Command.lean:637 | port (bootstrap no-arg command; trivial) |
| «docs_to_verso» | Lean.Parser.Command.«docs_to_verso» | Command.lean:642 | port |
| «deprecated_module» | Lean.Parser.Command.«deprecated_module» | Command.lean:656 | port |
| showDeprecatedModules | Lean.Parser.Command.showDeprecatedModules | Command.lean:663 | port |
| «set_option» | Lean.Parser.Command.«set_option» | Command.lean:682 | port (fixture-relevant: `set_option ... in <command>`) |
| «unlock_limits» | Lean.Parser.Command.«unlock_limits» | Command.lean:688 | port |
| «attribute» | Lean.Parser.Command.«attribute» | Command.lean:692 | port |
| «export» | Lean.Parser.Command.«export» | Command.lean:720 | port |
| «import» | Lean.Parser.Command.«import» | Command.lean:722 | port |
| «open» | Lean.Parser.Command.«open» | Command.lean:852 | port |
| «mutual» | Lean.Parser.Command.«mutual» | Command.lean:855 | port |
| «initialize» | Lean.Parser.Command.«initialize» | Command.lean:860 | port |
| «in» | Lean.Parser.Command.«in» | Command.lean:864 | port (`... in <command>` wrapper) |
| addDocString | Lean.Parser.Command.addDocString | Command.lean:889 | port |
| «register_tactic_tag» | Lean.Parser.Command.«register_tactic_tag» | Command.lean:897 | port |
| «tactic_extension» | Lean.Parser.Command.«tactic_extension» | Command.lean:907 | port |
| «recommended_spelling» | Lean.Parser.Command.«recommended_spelling» | Command.lean:948 | port |
| genInjectiveTheorems | Lean.Parser.Command.genInjectiveTheorems | Command.lean:958 | port |
| «include» | Lean.Parser.Command.«include» | Command.lean:968 | port |
| «omit» | Lean.Parser.Command.«omit» | Command.lean:976 | port |
| registerErrorExplanationStx | Lean.Parser.Command.registerErrorExplanationStx | Command.lean:1008 | port |
| «mixfix» | Lean.Parser.Command.«mixfix» | Syntax.lean:92 | **defer** — ParserDescr-producing notation DSL; parsing its own shape is trivial, but it exists only to *register* a parser extension, meaningless before M3b's ParserDescr interpreter. Lands M3b. |
| «notation» | Lean.Parser.Command.«notation» | Syntax.lean:95 | **defer** — same reason as «mixfix» |
| «macro_rules» | Lean.Parser.Command.«macro_rules» | Syntax.lean:102 | **defer** — pattern-matches against quotations; needs antiquotation + macro-expansion machinery. M3b/M4. |
| «syntax» | Lean.Parser.Command.«syntax» | Syntax.lean:105 | **defer** — ParserDescr-producing. M3b |
| syntaxAbbrev | Lean.Parser.Command.syntaxAbbrev | Syntax.lean:108 | **defer** — ParserDescr-producing. M3b |
| syntaxCat | Lean.Parser.Command.syntaxCat | Syntax.lean:113 | **defer** — declares a new parser *category*; meaningless before the category/extension machinery lands. M3b |
| «macro» | Lean.Parser.Command.«macro» | Syntax.lean:119 | **defer** — ParserDescr + macro-expansion. M3b |
| «elab_rules» | Lean.Parser.Command.«elab_rules» | Syntax.lean:122 | **defer** — same shape as macro_rules, targets elaborators. M3b/M4 |
| «elab» | Lean.Parser.Command.«elab» | Syntax.lean:127 | **defer** — ParserDescr-producing. M3b |
| binderPredicate | Lean.Parser.Command.binderPredicate | Syntax.lean:137 | **defer** — ParserDescr-producing (`binder_predicate` registers a new binder notation). M3b |
| grindPattern | Lean.Parser.Command.grindPattern | Lean/Meta/Tactic/Grind/Parser.lean:140 | port (fixed shape: ident, `=>`, term list; grind-specific but trivial to parse) |
| initGrindNorm | Lean.Parser.Command.initGrindNorm | Lean/Meta/Tactic/Grind/Parser.lean:143 | port |

Command category: 52 port, 10 defer (all 10 defers are the
ParserDescr-registration commands in `Syntax.lean` — `mixfix`,
`notation`, `macro_rules`, `syntax`, `syntaxAbbrev`, `syntaxCat`,
`macro`, `elab_rules`, `elab`, `binderPredicate`). This is the single
most important defer cluster in the whole table: it is exactly "the
extensible grammar" the M3 decomposition assigns to M3b. **No M3a
fixture may contain a `syntax`/`notation`/`macro`/`macro_rules`/`elab`/
`elab_rules`/`mixfix`/`binder_predicate` command**, full stop — not just
"don't use the notation later," the declaration itself doesn't parse
under M3a's builtin-only snapshot.

## term category (`Lean/Parser/Term.lean`, `Term/Basic.lean`, `Lean/Parser/Command.lean` quot decls, `Lean/Elab/Term/TermElabM.lean`) — 112 (+1 outside `Lean/Parser/` = 113 term-category rows, `builtin_term_parser` total is 112 because the script's per-category count above already includes it — see note)

Note on the count: the script reports 112 `builtin_term_parser` hits
total; `elabToSyntax` is one of the 112 (not an addition to it) — it's
simply not under `Lean/Parser/`. Corrected above: 111 under
`Lean/Parser/` + 1 under `Lean/Elab/` = 112.

### Core literals/atoms — fixture-critical, all port

| parser | kind name | source | M3a status |
|---|---|---|---|
| ident | Lean.Parser.Term.ident | Term.lean:124 | port |
| num | Lean.Parser.Term.num | Term.lean:126 | port |
| scientific | Lean.Parser.Term.scientific | Term.lean:128 | port |
| str | Lean.Parser.Term.str | Term.lean:130 | port |
| char | Lean.Parser.Term.char | Term.lean:132 | port |
| type | Lean.Parser.Term.type | Term.lean:135 | port |
| sort | Lean.Parser.Term.sort | Term.lean:138 | port |
| prop | Lean.Parser.Term.prop | Term.lean:143 | port |
| «sorry» | Lean.Parser.Term.«sorry» | Term.lean:164 | port |
| cdot | Lean.Parser.Term.cdot | Term.lean:174 | port |
| typeAscription | Lean.Parser.Term.typeAscription | Term.lean:182 | port |
| tuple | Lean.Parser.Term.tuple | Term.lean:186 | port |
| paren | Lean.Parser.Term.paren | Term.lean:200 | port |
| anonymousCtor | Lean.Parser.Term.anonymousCtor | Term.lean:216 | port |
| hole | Lean.Parser.Term.hole | Term/Basic.lean:118 | port |
| syntheticHole | Lean.Parser.Term.syntheticHole | Term/Basic.lean:164 | port |
| omission | Lean.Parser.Term.omission | Term/Basic.lean:175 | port |

### Binders, arrows, control forms — fixture-critical (spec's acceptance bar names binders, `match`/`do`/`by`, `let`, `fun` explicitly), all port

| parser | kind name | source | M3a status |
|---|---|---|---|
| depArrow | Lean.Parser.Term.depArrow | Term.lean:256 | port |
| «forall» | Lean.Parser.Term.«forall» | Term.lean:259 | port |
| «match» | Lean.Parser.Term.«match» | Term.lean:330 | port |
| «nomatch» | Lean.Parser.Term.«nomatch» | Term.lean:338 | port |
| «nofun» | Lean.Parser.Term.«nofun» | Term.lean:340 | port |
| structInst | Lean.Parser.Term.structInst | Term.lean:351 | port |
| structInstDefault | Lean.Parser.Term.structInstDefault | Term.lean:368 | port |
| «fun» | Lean.Parser.Term.«fun» | Term.lean:385 | port |
| «let» | Lean.Parser.Term.«let» | Term.lean:550 | port |
| «have» | Lean.Parser.Term.«have» | Term.lean:558 | port |
| «let_fun» | Lean.Parser.Term.«let_fun» | Term.lean:563 | port |
| «let_delayed» | Lean.Parser.Term.«let_delayed» | Term.lean:568 | port |
| «let_tmp» | Lean.Parser.Term.«let_tmp» | Term.lean:574 | port |
| «haveI» | Lean.Parser.Term.«haveI» | Term.lean:577 | port |
| «letI» | Lean.Parser.Term.«letI» | Term.lean:580 | port |
| «letrec» | Lean.Parser.Term.«letrec» | Term.lean:721 | port |
| «suffices» | Lean.Parser.Term.«suffices» | Term.lean:225 | port |
| «show» | Lean.Parser.Term.«show» | Term.lean:227 | port |
| explicit | Lean.Parser.Term.explicit | Term.lean:232 | port |
| inaccessible | Lean.Parser.Term.inaccessible | Term.lean:238 | port |
| byTactic | Lean.Parser.Term.byTactic | Term.lean:107 | port (fixture-critical: `by` blocks) |
| «unsafe» | Lean.Parser.Term.«unsafe» | Term.lean:761 | port |
| «open» | Lean.Parser.Term.«open» | Command.lean:1018 | port (`open Foo in <term>` — term-scoped `open`, distinct from the command-category `«open»` above and the tactic-category `«open»` below) |
| «set_option» | Lean.Parser.Term.«set_option» | Command.lean:1025 | port (`set_option ... in <term>` — term-scoped, distinct from the command/tactic versions) |

### App/projection/structural machinery — fixture-critical, all port

| parser | kind name | source | M3a status |
|---|---|---|---|
| app | Lean.Parser.Term.app | Term.lean:892 | port (term application — the core Pratt-loop leading/trailing pair) |
| proj | Lean.Parser.Term.proj | Term.lean:906 | port |
| completion | Lean.Parser.Term.completion | Term.lean:908 | port |
| arrow | Lean.Parser.Term.arrow | Term.lean:910 | port |
| dotIdent | Lean.Parser.Term.dotIdent | Term.lean:924 | port |
| explicitUniv | Lean.Parser.Term.explicitUniv | Term.lean:943 | port |
| namedPattern | Lean.Parser.Term.namedPattern | Term.lean:948 | port |
| pipeProj | Lean.Parser.Term.pipeProj | Term.lean:957 | port |
| pipeCompletion | Lean.Parser.Term.pipeCompletion | Term.lean:959 | port |
| subst | Lean.Parser.Term.subst | Term.lean:974 | port |
| panic | Lean.Parser.Term.panic | Term.lean:988 | port |
| unreachable | Lean.Parser.Term.unreachable | Term.lean:991 | port |
| dbgTrace | Lean.Parser.Term.dbgTrace | Term.lean:997 | port |
| borrowed | Lean.Parser.Term.borrowed | Term.lean:406 | port |
| quotedName | Lean.Parser.Term.quotedName | Term.lean:409 | port |
| doubleQuotedName | Lean.Parser.Term.doubleQuotedName | Term.lean:416 | port |
| noindex | Lean.Parser.Term.noindex | Term.lean:747 | port |
| binrel | Lean.Parser.Term.binrel | Term.lean:764 | port |
| binrel_no_prop | Lean.Parser.Term.binrel_no_prop | Term.lean:767 | port |
| binop | Lean.Parser.Term.binop | Term.lean:770 | port |
| binop_lazy | Lean.Parser.Term.binop_lazy | Term.lean:773 | port |
| leftact | Lean.Parser.Term.leftact | Term.lean:777 | port |
| rightact | Lean.Parser.Term.rightact | Term.lean:781 | port |
| unop | Lean.Parser.Term.unop | Term.lean:784 | port |
| forInMacro | Lean.Parser.Term.forInMacro | Term.lean:787 | port |
| forInMacro' | Lean.Parser.Term.forInMacro' | Term.lean:789 | port |

### `do`-block term wrappers — fixture-critical, all port

| parser | kind name | source | M3a status |
|---|---|---|---|
| doForward | Lean.Parser.Term.doForward | Do.lean:228 | port |
| nestedAction | Lean.Parser.Term.nestedAction | Do.lean:24 | port |
| «do» | Lean.Parser.Term.«do» | Do.lean:325 | port |
| termUnless | Lean.Parser.Term.termUnless | Do.lean:334 | port |
| termFor | Lean.Parser.Term.termFor | Do.lean:336 | port |
| termTry | Lean.Parser.Term.termTry | Do.lean:338 | port |
| termReturn | Lean.Parser.Term.termReturn | Do.lean:344 | port |

### Elaborator-internal pragma terms — obscure, syntactically trivial, no M3b dependency: port (same "obscure but trivial" logic as `#exit`)

| parser | kind name | source | M3a status |
|---|---|---|---|
| stateRefT | Lean.Parser.Term.stateRefT | Term.lean:1025 | port |
| showTermElabImpl | Lean.Parser.Term.showTermElabImpl | Term.lean:1034 | port |
| matchExpr | Lean.Parser.Term.matchExpr | Term.lean:1056 | port |
| letExpr | Lean.Parser.Term.letExpr | Term.lean:1059 | port |
| throwNamedErrorMacro | Lean.Parser.Term.throwNamedErrorMacro | Term.lean:1067 | port |
| throwNamedErrorAtMacro | Lean.Parser.Term.throwNamedErrorAtMacro | Term.lean:1076 | port |
| logNamedErrorMacro | Lean.Parser.Term.logNamedErrorMacro | Term.lean:1084 | port |
| logNamedErrorAtMacro | Lean.Parser.Term.logNamedErrorAtMacro | Term.lean:1093 | port |
| logNamedWarningMacro | Lean.Parser.Term.logNamedWarningMacro | Term.lean:1101 | port |
| logNamedWarningAtMacro | Lean.Parser.Term.logNamedWarningAtMacro | Term.lean:1110 | port |
| declName | Lean.Parser.Term.declName | Term.lean:793 | port |
| «privateDecl» | Lean.Parser.Term.«privateDecl» | Term.lean:796 | port |
| withDeclName | Lean.Parser.Term.withDeclName | Term.lean:805 | port |
| typeOf | Lean.Parser.Term.typeOf | Term.lean:807 | port |
| ensureTypeOf | Lean.Parser.Term.ensureTypeOf | Term.lean:809 | port |
| ensureExpectedType | Lean.Parser.Term.ensureExpectedType | Term.lean:811 | port |
| noImplicitLambda | Lean.Parser.Term.noImplicitLambda | Term.lean:813 | port |
| «inferInstanceAs» | Lean.Parser.Term.«inferInstanceAs» | Term.lean:846 | port |
| valueOf | Lean.Parser.Term.valueOf | Term.lean:851 | port |
| clear | Lean.Parser.Term.clear | Term.lean:858 | port |
| letMVar | Lean.Parser.Term.letMVar | Term.lean:861 | port |
| waitIfTypeMVar | Lean.Parser.Term.waitIfTypeMVar | Term.lean:863 | port |
| waitIfTypeContainsMVar | Lean.Parser.Term.waitIfTypeContainsMVar | Term.lean:865 | port |
| waitIfContainsMVar | Lean.Parser.Term.waitIfContainsMVar | Term.lean:867 | port |
| defaultOrOfNonempty | Lean.Parser.Term.defaultOrOfNonempty | Term.lean:870 | port |
| noErrorIfUnused | Lean.Parser.Term.noErrorIfUnused | Term.lean:877 | port |
| «idbg» | Lean.Parser.Term.«idbg» | Term.lean:1001 | port |
| assert | Lean.Parser.Term.assert | Term.lean:1005 | port |
| debugAssert | Lean.Parser.Term.debugAssert | Term.lean:1011 | port |
| elabToSyntax (`_root_.Lean.Parser.Term.elabToSyntax`) | Lean.Parser.Term.elabToSyntax | Lean/Elab/Term/TermElabM.lean:815 | port (fixed `elabToSyntax% <numLit>` shape) |

### Parser-authoring meta-DSL — port (trivial wrapper syntax; some Mathlib meta files define custom `Parser`s directly this way)

| parser | kind name | source | M3a status |
|---|---|---|---|
| «leading_parser» | Lean.Parser.Term.«leading_parser» | Term.lean:392 | port |
| «trailing_parser» | Lean.Parser.Term.«trailing_parser» | Term.lean:394 | port |

### Quotation family — **defer**, explicitly called out by the task brief as the paradigm case

| parser | kind name | source | M3a status |
|---|---|---|---|
| Term.quot | Lean.Parser.Term.quot | Command.lean:20 | **defer** — syntax quotation `` `(term) `` ; meaningless without antiquotation machinery, lands with M3b |
| Term.precheckedQuot | Lean.Parser.Term.precheckedQuot | Command.lean:22 | **defer** — same reason |
| quot | Lean.Parser.Command.quot | Command.lean:50 | **defer** — command-category quotation, same reason |
| dynamicQuot | Lean.Parser.Term.dynamicQuot | Term.lean:1028 | **defer** — same reason |
| Tactic.quot | Lean.Parser.Tactic.quot | Term.lean:1123 | **defer** — same reason |
| Tactic.quotSeq | Lean.Parser.Tactic.quotSeq | Term.lean:1125 | **defer** — same reason |

Term category tally: 106 port, 6 defer (the quot family).

## do-element category (`Lean/Parser/Do.lean`) — 27, all port

Structurally trivial fixed-shape statements inside `do`-blocks; fixture
acceptance names `do` explicitly.

Kind-name note: every declaration in `Do.lean` sits inside that file's
own `namespace Term` (opened at `Do.lean:22`, nested under `namespace
Lean.Parser`) — `Do.lean` never opens a `namespace Do`. So despite the
category name `builtin_doElem_parser`, every kind name below is
`Lean.Parser.Term.do*`, not `Lean.Parser.Do.*`. Verified by tracing live
`namespace`/`end` nesting in the file directly (no `namespace Do` exists
anywhere in it) — exactly the kind of assumption the task brief warned
against baking in.

| parser | kind name | source | M3a status |
|---|---|---|---|
| doLet | Lean.Parser.Term.doLet | Do.lean:77 | port |
| doLetElse | Lean.Parser.Term.doLetElse | Do.lean:79 | port |
| doLetExpr | Lean.Parser.Term.doLetExpr | Do.lean:83 | port |
| doLetMetaExpr | Lean.Parser.Term.doLetMetaExpr | Do.lean:87 | port |
| doLetRec | Lean.Parser.Term.doLetRec | Do.lean:91 | port |
| doLetArrow | Lean.Parser.Term.doLetArrow | Do.lean:99 | port |
| doReassign | Lean.Parser.Term.doReassign | Do.lean:112 | port |
| doReassignArrow | Lean.Parser.Term.doReassignArrow | Do.lean:122 | port |
| doHave | Lean.Parser.Term.doHave | Do.lean:124 | port |
| doIf | Lean.Parser.Term.doIf | Do.lean:169 | port |
| doUnless | Lean.Parser.Term.doUnless | Do.lean:175 | port |
| doFor | Lean.Parser.Term.doFor | Do.lean:186 | port |
| doMatch | Lean.Parser.Term.doMatch | Do.lean:193 | port |
| doMatchExpr | Lean.Parser.Term.doMatchExpr | Do.lean:200 | port |
| doTry | Lean.Parser.Term.doTry | Do.lean:209 | port |
| doBreak | Lean.Parser.Term.doBreak | Do.lean:232 | port |
| doContinue | Lean.Parser.Term.doContinue | Do.lean:234 | port |
| doReturn | Lean.Parser.Term.doReturn | Do.lean:245 | port |
| doDbgTrace | Lean.Parser.Term.doDbgTrace | Do.lean:251 | port |
| doIdbg | Lean.Parser.Term.doIdbg | Do.lean:281 | port |
| doAssert | Lean.Parser.Term.doAssert | Do.lean:286 | port |
| doDebugAssert | Lean.Parser.Term.doDebugAssert | Do.lean:292 | port |
| doRepeat | Lean.Parser.Term.doRepeat | Do.lean:295 | port |
| doWhile | Lean.Parser.Term.doWhile | Do.lean:297 | port |
| doRepeatUntil | Lean.Parser.Term.doRepeatUntil | Do.lean:299 | port |
| doExpr | Lean.Parser.Term.doExpr | Do.lean:318 | port |
| doNested | Lean.Parser.Term.doNested | Do.lean:322 | port |

`doReassignElse` (would-be `Do.lean:118`) does **not** exist as a live
declaration — it's behind a `--` line comment in the pinned toolchain
source (disabled/unfinished feature). Confirmed no other definition
exists anywhere in `src/lean`. Not part of the porting surface; noted so
nobody goes looking for it.

## level category (`Lean/Parser/Level.lean`) — 7, all port

| parser | kind name | source | M3a status |
|---|---|---|---|
| paren | Lean.Parser.Level.paren | Level.lean:24 | port |
| max | Lean.Parser.Level.max | Level.lean:26 | port |
| imax | Lean.Parser.Level.imax | Level.lean:28 | port |
| hole | Lean.Parser.Level.hole | Level.lean:30 | port |
| num | Lean.Parser.Level.num | Level.lean:32 | port |
| ident | Lean.Parser.Level.ident | Level.lean:34 | port |
| addLit | Lean.Parser.Level.addLit | Level.lean:36 | port |

Small and self-contained (`Sort`/`Type` universe levels) — needed
wherever a fixture uses `Sort u`/`Type u`/`.{u, v}` universe params.

## tactic category (`Lean/Parser/Tactic.lean`, `Lean/Parser/Command.lean`) — 6

| parser | kind name | source | M3a status |
|---|---|---|---|
| «unknown» | Lean.Parser.Tactic.«unknown» | Tactic.lean:29 | port — fallback/error-recovery node for unrecognized tactic syntax; needed for the "parse errors are values" guarantee |
| nestedTactic | Lean.Parser.Tactic.nestedTactic | Tactic.lean:32 | port |
| «match» | Lean.Parser.Tactic.«match» | Tactic.lean:50 | port |
| introMatch | Lean.Parser.Tactic.introMatch | Tactic.lean:55 | port |
| «open» | Lean.Parser.Tactic.«open» | Command.lean:1032 | port (`open Foo in <tactic>`) |
| «set_option» | Lean.Parser.Tactic.«set_option» | Command.lean:1037 | port (`set_option ... in <tactic>`) |

As the design spec predicted, the tactic category is tiny — almost
every real tactic (`exact`, `intro`, `simp`, `rfl`, …) is declared via
`syntax`/`macro` in `Init/`, not compiled. This is exactly the M3a/M3b
line the brief is drawing: M3a can parse *that* a tactic sequence
exists (`by <nestedTactic>`, unknown-tactic recovery, `match` inside
tactic position, `introMatch`) but cannot name almost any specific
tactic without M3b's ParserDescr.

## syntax category (`Lean/Parser/Syntax.lean`) — 9, all port

The ParserDescr *primitive combinators* themselves (used to write the
bodies of `syntax`/`notation` declarations, which are deferred above).
These are compiled, trivial, and needed regardless of whether the
declarations that use them are interpreted — porting them costs nothing
and keeps the category boundary exactly at "ParserDescr interpretation",
not "every parser touching ParserDescr's vocabulary."

| parser | kind name | source | M3a status |
|---|---|---|---|
| paren | Lean.Parser.Syntax.paren | Syntax.lean:37 | port |
| cat | Lean.Parser.Syntax.cat | Syntax.lean:39 | port |
| unary | Lean.Parser.Syntax.unary | Syntax.lean:41 | port |
| binary | Lean.Parser.Syntax.binary | Syntax.lean:43 | port |
| sepBy | Lean.Parser.Syntax.sepBy | Syntax.lean:45 | port |
| sepBy1 | Lean.Parser.Syntax.sepBy1 | Syntax.lean:48 | port |
| atom | Lean.Parser.Syntax.atom | Syntax.lean:51 | port |
| nonReserved | Lean.Parser.Syntax.nonReserved | Syntax.lean:54 | port |
| unicodeAtom | Lean.Parser.Syntax.unicodeAtom | Syntax.lean:57 | port |

## struct-instance-field-decl category (`Lean/Parser/Term.lean`) — 2, both port

| parser | kind name | source | M3a status |
|---|---|---|---|
| structInstFieldDef | Lean.Parser.Term.structInstFieldDef | Term.lean:357 | port |
| structInstFieldEqns | Lean.Parser.Term.structInstFieldEqns | Term.lean:360 | port |

(`structInstFieldWhere` is documentation prose only, see enumeration
notes — no live declaration.)

## misc singleton categories — 2, both port

| parser | kind name | attribute | source | M3a status |
|---|---|---|---|---|
| numPrec | Lean.Parser.Syntax.numPrec | builtin_prec_parser | Syntax.lean:35 | port |
| numPrio | Lean.Parser.Priority.numPrio | builtin_prio_parser | Attr.lean:33 | port |

## deliberately deferred inside M3a — full list (16 declarations)

All 16 defers fall into exactly two clusters, both explicitly the
"needs M3b/M4 machinery to mean anything" case the brief describes —
there is no ad hoc defer in this table:

- **ParserDescr-registration commands (10):** `mixfix`, `notation`,
  `macro_rules`, `syntax`, `syntaxAbbrev`, `syntaxCat`, `macro`,
  `elab_rules`, `elab`, `binderPredicate` — all in `Syntax.lean`. Parsing
  their own keyword+argument shape is mechanically easy, but the entire
  point of the declaration is to register a `ParserDescr` (a value M3a
  has no interpreter for) or, for `macro_rules`/`elab_rules`, to
  pattern-match against syntax quotations (needs antiquotation, below).
  Lands with M3b (`ParserDescr` interpreter + same-file
  `syntax`/`notation`/`macro` commands — named explicitly in the M3a/M3b
  split in the parent design spec).
- **Quotation family (6):** `Term.quot`, `Term.precheckedQuot`, `quot`
  (command-category), `dynamicQuot`, `Tactic.quot`, `Tactic.quotSeq`.
  Parsing `` `(e) `` requires antiquotation (`$x`) support baked into
  the same grammar traversal — not meaningful in isolation, and every
  consumer of quotations (`macro_rules`, `elab_rules`) is deferred
  anyway. Lands with M3b.

Everything else — 223 of 239 declarations — is **port**. This matches
the brief's stated default ("M3a's builtin snapshot should BE the
builtin grammar, not a curated subset"): the only real carve-out is the
extensible-grammar registration surface itself, which is what M3b
exists to build.

## fixture-authoring constraints (derived)

- **No Init notation at all.** No `+ - * / < > ≤ ≥ ∘ ∈ ∧ ∨ ¬ ↔ ×` or any
  other infix/prefix operator, no `<|>`, no list `[a, b, c]` notation,
  no anonymous-constructor sugar beyond the builtin `⟨...⟩`
  (`anonymousCtor` ports; the notations built *on* it like `(a, b)`
  tuple-via-`Prod.mk` do not — `(a, b)` itself is fine, it's the builtin
  `tuple`/`paren` parser, but don't assume `HAdd.hAdd`-style operator
  sugar works). Every one of `+ - * = < >` is `Init`-declared
  `notation`/`infix`, never a builtin parser.
- **No Init tactics.** `exact`, `intro`, `rfl`, `simp`, `apply`, `rw`, …
  are all `syntax`-declared in `Init/`. Only `Tactic.lean`'s tiny builtin
  set is available: bare `by <seq>` structurally, `match` in tactic
  position, `introMatch`, and the `«unknown»` error-recovery node
  (meaning an actually *invalid* tactic still round-trips through an
  error node — that's testable, a *valid* named tactic is not).
- **No `syntax`/`notation`/`macro`/`macro_rules`/`elab`/`elab_rules`/
  `mixfix`/`binder_predicate` commands**, same-file or otherwise — the
  declaration's own syntax doesn't parse under M3a's builtin-only
  snapshot (see command-category table above). This is stronger than
  "don't use the declared notation later" — the declaration line itself
  is out.
- **No syntax quotations** (`` `(term) ``, `` `(tactic| ...) ``, etc.)
  anywhere, including inside otherwise-portable constructs — the quot
  family is deferred regardless of context.
- **OK:** numerals, string/char literals, scientific literals,
  identifiers (incl. French-quote `«...»` idents), `fun`/`∀`
  (`unicodeAtom`-backed `«forall»`)/`let`/`letI`/`haveI`/`let_fun`/
  `letrec`/`match`/`nomatch`/`nofun`/`do`/`by`, `def`/`theorem`/
  `instance`/`structure`-shaped `declaration`, `deriving` clauses
  (syntactic only), `set_option ... in`, `open`/`namespace`/`section`/
  `end`/`variable`/`universe`, term application/projection/`.dotIdent`
  completion, anonymous constructors `⟨...⟩`, struct-instance literals
  `{ ... with ... }`, `show`/`suffices`, dependent arrows `(x : A) → B`,
  `Sort`/`Type` universes.
- Anything using an *operator* to combine two terms (arithmetic,
  comparison, boolean connectives, `∘`, `<|>`, …) is unavailable until
  M3b, because every such operator is `Init`-declared infix notation,
  not a builtin parser — this is by far the most consequential
  constraint for fixture authors: it rules out ordinary arithmetic
  expressions entirely, even `1 + 1`.
