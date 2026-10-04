# M4c-2b-i — scopes, declaration names and `resolveGlobalName` — design

Status: approved in brainstorming 2026-10-04 (architectural path).
Second slice of M4c-2, after M4c-2a shipped (#72, cf66ceb).

Pinned oracle: `leanprover/lean4:v4.33.0-rc1`. The citations below were
opened against that toolchain's `src/lean/Lean` while writing this spec.
They are still subject to the "verify at plan time" rule (cites drift by
1-2 lines).

## Goal

M4c-2a elaborates a header-less source of many commands, but every command
runs at the root namespace with nothing opened, and any scope command stops
the loop with a seam. This slice adds the oracle's command scopes
(`namespace`/`section`/`end`/`open`), the namespace-aware declaration name
(`mkDeclName`: dotted, `_root_`, `protected`), and the oracle's full global
name resolution (`ResolveName.resolveGlobalName`) with the environment
tables it reads (protected names, namespaces, aliases). The result is
differential-tested per command through the M4c-2a file gate.

**Success:**
- Every new file-corpus record elaborates as the oracle does: per command,
  the same constants (full `ConstantInfo`, aux before main), or, for a last
  command that errors, the same first error line.
- An identifier with two or more resolution candidates fails with the named
  seam `— M4c-2b-ii`, never by silently picking one.
- A reference the oracle resolves to the current declaration's own aux
  local (a recursive reference) fails with a named seam, never by resolving
  to a same-named global.
- Every other out-of-scope command or modifier fails with a named seam.
- Every existing corpus stays green. After the `Elab0` append, every
  committed `*.jsonl` corpus regenerates byte-identical.

## Decomposition (agreed)

M4c-2b, as named in the M4c-2a spec, splits in two:
- **M4c-2b-i (this spec):** scope state and scope commands, declaration-name
  expansion, `resolveGlobalName` with every `open` form, and decoding of
  `protectedExt`, `namespacesExt` and `aliasExtension`. More than one
  candidate is a seam.
- **M4c-2b-ii:** overloaded elaboration. `elabAppAux` with several
  candidates: try each, keep the successes, report ambiguity,
  `mergeFailures`.

M4c-2c (`universe`/`variable`/auto-bound) is unchanged.

## User decisions

1. **Split (A).** Multiple candidates are reachable without `open` (the
   enclosing-namespace walk, root plus alias), so overloaded elaboration is
   its own slice. Until it lands, the resolver returns the full candidate
   list and every caller that needs one seams on more.
2. **`Elab0` append (A).** The imported-side decoders get oracle coverage
   from a small block appended to `tests/fixtures/elab/Elab0.lean` (a
   `protected` declaration, nested namespaces, an `export`). The regen must
   leave every committed corpus byte-identical. Rejected: a frozen `Elab0`
   with unit-only decoder coverage (B), and a second prelude fixture (C).
3. **Approach 1.** The scope state mirrors `Command.Scope` on `CommandElab`.
   The three tables are owned by the elaborator (`leanr_elab`), decoded by
   `leanr_olean` and passed to `CommandElab::new`. They are NOT added to
   `leanr_meta::EnvExtensions`: meta never reads them, and `leanr_meta/src`
   stays untouched. Rejected: syntactic desugaring to fully qualified names
   (resolution is semantic: walk order, atomic-only `protected`, `hiding`).

Defaults accepted with the design:
- `private`, the `export` command, `open scoped`, `noncomputable`/`public`/
  `meta`/`@[expose]` sections and term-level `open … in` stay seams
  (later M4). Imported aliases are honoured by resolution.
- Reserved names (`realizeGlobalName`, `f.eq_1`) stay out.
- The delaborator's name shortening (`unresolveNameGlobal`) stays out. No
  gated first line needs it: "has already been declared" prints with
  `.ofConstName n true`, full names (`Elab/DeclModifiers.lean:43`), and
  `UnknownIdent` echoes the raw source text.

## The oracle model

### Scopes

- `Command.Scope` holds `header`, `currNamespace` and `openDecls` (plus
  level names, variables and modifier flags owned by M4c-2c and later).
  `scopes` is a non-empty list whose last element is the anonymous root
  scope.
- `addScope` (`Elab/BuiltinCommand.lean:45-60`) pushes a copy of the head
  scope with a new header and namespace, and calls `registerNamespace`.
  `activateScoped` runs for a new namespace. That has no effect here, since
  Elab0 declares no `scoped` entries and the `scoped` attribute kind is
  already a seam.
- `addScopes` (`:62-71`) pushes one scope per component of `A.B`, with
  namespace `curr ++ A`, then `curr ++ A ++ B`. For a `section` the
  namespace stays the current one.
- `elabNamespace` (`:101`) and `elabSection` (`:106-118`). A section with
  `noncomputable`, `public`, `meta` or `@[expose]` is a seam here.
- `elabEnd` (`:241-266`): `endSize` is 1 without a header, otherwise the
  header's component count. Its errors, in check order:
  - only the root scope is open: `Invalid \`end\`: There is no current
    scope to end` (`throwNoScope`);
  - no header but the innermost scope is named: `Missing name after
    \`end\`: Expected the current scope name \`N\``;
  - `endSize >= numScopes`: `Invalid name after \`end\`: \`H\` contains
    too many components`;
  - the scopes' names differ: `Unexpected name \`H\` after \`end\`: The
    current section is unnamed` when they are anonymous, otherwise
    `Invalid name after \`end\`: Expected \`S\`, but found \`H\``.

  Then it drops `endSize` scopes.
- `elabOpen` (`:312-316`) replaces the head scope's `openDecls` with
  `elabOpenDecl`'s result (`Elab/Open.lean:74-119`):
  - `open A B` resolves each namespace (`resolveNamespace`, every
    interpretation) and adds `OpenDecl.simple ns []`;
  - `open A (x y)` resolves each id in the namespaces
    (`resolveNameUsingNamespacesCore`, `:53-72`) and adds
    `OpenDecl.explicit x declName`;
  - `open A hiding x` needs a unique namespace, checks `x` resolves in it,
    and adds `OpenDecl.simple A [x]`;
  - `open A renaming x → y` needs a unique namespace and adds
    `OpenDecl.explicit y declName`;
  - `open scoped` is a seam.
- `expandInCmd` (`:532-536`): `cmd₁ in cmd₂` is `section cmd₁
  end_local_scope cmd₂ end`. `end_local_scope` (`setDelimitsLocal`) only
  touches scoped extensions, so it is inert here.

### Declaration names

- `expandNamespacedDeclaration` (`Elab/Declaration.lean:150-159`) with
  `expandDeclNamespace?` (`:90-102`): `def A.B.f` becomes
  `namespace A.B end_local_scope def f end A.B`. A `_root_`-prefixed name is
  not expanded. Its namespace is only checked (`ensureValidNamespace`). An
  atomic name is not expanded either.
- `mkDeclName` (`Elab/DeclModifiers.lean:263-286`):
  - ``invalid declaration name `_root_` `` for the bare name;
  - `_root_.p.s` gives `p.s`, with short name `s` and namespace `p`;
  - otherwise the result is `currNamespace ++ shortName`;
  - `protected` returns short name `ns.last ++ shortName`. In the root
    namespace with an atomic short name it is the error `protected
    declarations must be in a namespace`.
- `registerNamePrefixes` (`AddDecl.lean:54-62`, run on every `addDecl` at
  `:107`) registers each proper prefix of an added name as a namespace.
  It skips a name whose last component starts with `_`.

### Resolution

`ResolveName.resolveGlobalName` (`ResolveName.lean:194-216`): `loop` strips
trailing components into `projs`. For each remaining `id`:
1. `resolveUsingNamespace` (`:146-151`): for `ns` and then each of its
   prefixes, innermost first, `resolveQualifiedName ns id` (`:134-143`).
   That returns `ns ++ id` if it is declared and not (protected with `id`
   atomic), plus the aliases of `ns ++ id` (protected ones skipped for
   atomic `id`). The first namespace with any hit wins.
2. Otherwise `resolveExact` (`:154-162`), for non-atomic `id` only: `id`
   with `_root_` replaced, if declared, gives a single result.
3. Otherwise: `[id]` if declared; then `resolveOpenDecls` (`:165-185`)
   (`simple ns exs`: `resolveQualifiedName ns id` unless `id ∈ exs`;
   `explicit o r`: `r` when `o == id`, `id` with prefix `o` replaced by `r`
   when that is declared); then `getAliases id (skipProtected :=
   id.isAtomic)` prepended. A non-empty result is returned (`eraseDups`).
   An empty one continues the loop.

`resolvePrivateName` is unreachable with no header and `private` seamed.

Namespaces: `resolveNamespace` (`:252-255`) =
`resolveNamespaceUsingScope?` (`:220-230`, innermost first, `_root_`
stripped at the root) followed by `resolveNamespaceUsingOpenDecls`
(`:232-239`). The empty case is ``unknown namespace `X` `` (`:337`).
`resolveUniqueNamespace` gives ``ambiguous namespace `X`, possible
interpretations: …`` (`:356`).

`resolveLocalName` (`ResolveName.lean:460-622`): its `loop` tries
ever-shorter prefixes. Each step searches the local context: a regular local
matches by user name, and an aux local (a declaration being defined) by
`matchAuxRecDecl?` (`:497-548`). If `currNamespace` is a prefix of the full
name, the match is relaxed: the local's name must be a suffix of the given
name, and the given name a suffix of the full name. Otherwise `ns ++ given`
must equal the full name for some prefix `ns` of the namespace. Then comes an
exact-name retry over aux locals. `globalDeclFound` skips aux locals once a
shorter prefix has resolved globally with projections pending.

`MutualDef.lean:359-366` (`withFunLocalDecls`) installs an aux local
(`withAuxDecl shortDeclName type declName`) for every def/theorem header
before elaborating bodies. `elabAxiom` installs none.

## Architecture

### Decoding (`leanr_olean`, additive)

Three typed `ModuleData` fields, each decoded by extension name in
`interp_id.rs` next to `elabAsElim`:
- `Lean.protectedExt` → `protected_names: Vec<NameId>` (tag extension).
- `Lean.namespacesExt` → `namespaces: Vec<NameId>`.
- `Lean.aliasExtension` → `aliases: Vec<(NameId, NameId)>` (alias →
  target).

The plan pins each entry's on-disk shape from the oracle source and a probe
before writing the decoder. Malformed bytes give an `Err`, never a panic
(`docs/THREAT_MODEL.md`), and each decoder gets a decode-error test.

### `NameTables` (`leanr_elab/src/names.rs`, new)

```rust
pub struct NameTables {
    protected: HashSet<NameId>,
    namespaces: HashSet<NameId>,
    aliases: HashMap<NameId, Vec<NameId>>,
}
```

Queries: `is_protected`, `is_namespace`, `get_aliases(id, skip_protected)`.
Mutators: `register_namespace`, `register_name_prefixes`, `add_protected`.
Owned by `CommandElab`, because the file grows it. Built in
`CommandElab::new` from the three decoded slices. Every existing caller
(test support, the harness) passes them from `ModuleData`.

### Scope state and the command layer (`leanr_elab/src/command/scope.rs`, new)

```rust
pub(crate) struct Scope { header: String, curr_namespace: NameId, open_decls: Vec<OpenDecl> }
pub enum OpenDecl { Simple { ns: NameId, except: Vec<NameId> }, Explicit { id: NameId, decl: NameId } }
```

`CommandElab` gains `scopes: Vec<Scope>`, whose bottom entry is the root.
M4c-2c adds level names and variables to `Scope`. `elab_commands`
dispatches on the command kind:
- **Ported here:** `namespace`, `section`, `end`, `open` and `in`. Each
  follows the oracle model above, with the oracle's first error lines.
- **Declarations:** run `expandNamespacedDeclaration` (push the namespace
  scopes, elaborate with the short name, pop), then the existing
  `elab_decl` path.
- **Everything else:** keeps the M4c-2a seam table.

`command_seam`'s M4c-2b arm is removed. The remaining M4c-2b seams carry
precise labels: `open scoped`, modified `section` and term-level `open` are
`later M4`.

`header.rs`'s `expandDeclId` ports `mkDeclName`, replacing the
`view.rs` seams for dotted, `_root_` and `protected` names. After each
admitted declaration (aux and main), `register_name_prefixes` runs on its
name. A `protected` declaration is added to the protected set when it is
admitted.

### Resolution (`leanr_elab/src/resolve.rs`)

```rust
pub struct ResolveCtx<'a> {
    pub ns: NameId,
    pub open_decls: &'a [OpenDecl],
    pub tables: &'a NameTables,
    pub aux_decl: Option<AuxDecl>, // the current declaration: full + short name
}
```

`TermElabM` holds a `ResolveCtx`. `CommandElab` builds it from the
innermost scope. Term-only harnesses (`oracle_elab`, the smoke tests) get
the root context (anonymous namespace, no opens, empty tables, no aux
declaration), so their behaviour is unchanged.

- **`resolve_global_name`** becomes `resolveGlobalName` and returns
  `Vec<(NameId, usize)>`. It ports steps 1–3 above and the `loop`.
- **`resolve_local_name`** ports `resolveLocalName`'s `loop`, including
  `globalDeclFound`/`skipAuxDecl`, which calls the new global resolver.
  It also ports `matchAuxRecDecl?` and the exact retry against
  `ResolveCtx.aux_decl`. leanr builds no aux local, so a hit returns
  `UnsupportedSyntax("recursive reference to \`f\` — later M4
  (recursion)")`. Axioms set `aux_decl = None`. The plan probes whether
  `theorem` and `example` install the aux local and sets it per kind
  accordingly.
- **Namespace resolution:** `resolve_namespace`, `resolve_unique_namespace`
  and `resolve_name_using_namespaces` serve `open` and `_root_.A.x`
  validity.

Callers:
- **`app/head.rs` and `builtin/op/mod.rs`:** one candidate takes today's
  path. Two or more is `UnsupportedSyntax("overloaded identifier \`x\` (n
  candidates) — M4c-2b-ii")`. `app/overload.rs`'s guard message is
  relabelled `— M4c-2b-ii`.
- **`builtin/binder/fun.rs` (`names_a_global`):** a non-empty candidate list
  means a global, as in the oracle (`Binders.lean:384`). No seam is needed.
- **`builtin/lit/mod.rs` (`const_with_level`, `const_no_levels`):** these
  settle the decision recorded in their doc. They bypass the resolver for an
  absolute `view.get(name)`, matching the oracle's compile-time
  ``` ``OfNat ``` (`BuiltinTerm.lean`). A user `OfNat` in an opened
  namespace cannot retarget a numeral.

## Harness

There are no new mechanics. Records are added to `fileQueries` in
`tests/fixtures/elab/dump_decls.lean` (files mode), and
`crates/leanr_elab/tests/oracle_file.rs` gates them unchanged. Dumped
constant names are fully qualified, so namespaced declarations compare
exactly. The parse-only test covers every new source.

At plan time, confirm that leanr's grammar parses the following:
- `namespace` and `end` forms;
- every `open` form;
- `open … in`;
- `section`;
- `protected`, `_root_.` and dotted declaration ids.

`CORPUS_FLOOR` rises to the new record count.

### `Elab0` append

A tail block in `tests/fixtures/elab/Elab0.lean`, final names settled by
probe:

```lean
namespace Scope0
protected def hidden : Nat := Nat.zero
def shown : Nat := Nat.zero
namespace Inner
def deep : Nat := Nat.zero
end Inner
end Scope0
namespace Scope0Exp
def ex : Nat := Nat.zero
end Scope0Exp
export Scope0Exp (ex)
```

The regen (`mise run fixtures:regen` and the decl regen) must leave every
committed `*.jsonl` corpus byte-identical. The only expected changes are
`Elab0.olean` and any fixture that enumerates all of Elab0's constants. Any
other change is a finding to rule on, not to accept.

### Corpus

About 25–30 new records, every one oracle-probed at plan time:
- **Scopes:**
  - `namespace A … end A`;
  - nested `A.B`, closed by `end A.B`, and by `end B` then `end A`;
  - `section` with and without a name;
  - a declaration inside each.
- **Declaration names:**
  - dotted `def A.f` referencing a sibling `A.g` by its short name;
  - `def A.f` without `namespace A`;
  - `_root_.x` from inside a namespace;
  - `protected def A.p`, then `A.p` resolving.
- **Resolution:**
  - an enclosing-namespace walk where the inner hit wins;
  - root fallback;
  - a trailing field split under a namespace;
  - imported `Scope0.shown` and `Scope0.Inner.deep` via `open Scope0`;
  - the imported alias `ex`.
- **`open` forms:**
  - simple, `(ids)`, `hiding`, `renaming`, `open … in`;
  - `_root_.Ns.x`;
  - an explicit `open` whose renamed name is a prefix of a longer id.
- **Errors, as the last command:**
  - each `end` error;
  - `unknown namespace`;
  - `protected declarations must be in a namespace`;
  - ``invalid declaration name `_root_` ``;
  - `open X (nope)`;
  - ``Unknown identifier`` for a protected short name (file-local and the
    imported `Scope0.hidden` after `open Scope0`);
  - an identifier hidden by `hiding`.

### Unit pins

These are cases a gated corpus cannot reach:
- **Two candidates:** an enclosing-namespace hit plus an `open` hit seams
  `— M4c-2b-ii`. So does the root plus an alias.
- **Recursive reference:** `namespace A` then `def x : Nat := x`, with a
  root `x` in scope, seams `recursive reference`. Today this would be a
  wrong `Ok`.
- **Numerals:** a user `namespace X` with its own `OfNat` and `open X`
  never retargets a numeral.
- **Tables:**
  - the `NameTables` queries;
  - `register_name_prefixes` skipping `_` components;
  - each decoder's malformed-byte `Err`.
- **Remaining seams:** `open scoped`, `noncomputable section` and
  term-level `open … in`, each with its label.
- **Replaced:** `scope_commands_are_m4c2b_seams` is replaced by these pins.

### Mutations the plan records

Each must fail a named test:
- the namespace walk visits outermost first;
- `protected` is not skipped for atomic ids;
- `hiding`'s `except` is ignored;
- `resolveExact` is applied to atomic ids;
- `end` pops one scope instead of `endSize`;
- `register_name_prefixes` is dropped;
- the aux-decl matcher is disabled;
- the numeral path goes back through the resolver;
- the resolver returns only the first candidate instead of all of them.

## Out of scope (named seams or unchanged)

- **M4c-2b-ii:** overloaded elaboration.
- **Later M4:**
  - `export` (the command);
  - `private`;
  - `open scoped` and `activateScoped`;
  - `noncomputable`/`public`/`meta`/`@[expose]` sections;
  - term-level `open … in`;
  - recursion, including a recursive reference;
  - reserved names;
  - the delaborator's name shortening.
- **M4c-2c:** `universe`, `variable`, auto-bound implicits.
- **Unchanged from M4c-2a:**
  - stop at the first error;
  - no module header;
  - the compile-error blind spot.

## Suggested plan shape

1. Decoders, the `Elab0` append, and a regen with the byte-identical check.
2. `NameTables`, the scope state and the command layer (`scope.rs`,
   `mkDeclName`, `expandNamespacedDeclaration`).
3. The resolver, `ResolveCtx`, and the caller migration, including the
   numeral bypass.
4. The aux-decl matcher (`resolveLocalName` port).
5. Corpus, docs (`resolve.rs`'s module doc, the `lib.rs` deferral ledger,
   `dispatch.rs`), and a § Landed section.
