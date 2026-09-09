# `elimMVarDeps` blast radius — findings

Measured at commit `95e45508de831e73688c44a6c83dd16ab0a283f7` with the temporary
`mk_binding` probe described in the implementation plan's Task 1. The probe
reports every `mk_binding` call whose body carries an unassigned metavariable
whose own declared local context contains a telescope free variable — exactly
the population whose behavior `elim_mvar_deps` changes.

## Totals

| Corpus | `mk_binding` calls hit | distinct records affected |
| --- | --- | --- |
| `oracle_elab` (113 records) | 1 | 1 |
| `oracle_synth` (24 compared) | 0 | 0 |
| `oracle_fast` | 0 | 0 |
| `leanr_meta` unit tests | 0 | — |

Note: the plan's Task 1 brief template shows "oracle_elab (107 records)" as
illustrative text. The corpus committed at this commit has 113 records
(`wc -l tests/fixtures/elab/elab-queries.jsonl` = 113, matching
`oracle_elab.rs`'s own `CORPUS_FLOOR = 113`); 113 is the actual, observed
count and is what is reported here.

## Affected records

- `tc/funWrapElided` (`oracle_elab`) — one unassigned `Synthetic` mvar
  (`MVarId(NameId(2147483678))`) in scope of the telescope being abstracted,
  on a `mk_lambda` call (`is_lambda=true`).

No other record, in any of the four corpora, tripped the probe.

## Kinds observed

| `MVarKind` | count | branch it will take in `elim_mvar` |
| --- | --- | --- |
| `Natural` | 0 | plain assign |
| `Synthetic` | 1 | plain assign |
| `SyntheticOpaque` | 0 | delayed |

## What this means for Task 10

Exactly one record across all four committed corpora — `tc/funWrapElided` in
`oracle_elab` — currently exercises the gap: a `mk_lambda` call whose body
holds an unassigned `Synthetic` mvar in scope of the fvars being abstracted.
Every other record in `oracle_elab` (112 of 113), all 24 compared
`oracle_synth` records, all of `oracle_fast`, and all `leanr_meta` unit tests
are unaffected — `elim_mvar_deps` is a no-op for them, so Task 10's
byte-identical gate should see them move by exactly zero bytes. `tc/funWrapElided`
is the one record to watch: since its mvar is `Synthetic` (plain-assign
branch, not delayed), and the corpus's own byte comparison currently passes —
meaning today's plain `abstract_fvars` already happens to produce the right
answer for it, per the brief's "right by accident" framing — a `elim_mvar_deps`
port that changes this record's output bytes is the first and only thing to
investigate as a possible regression; if it changes nothing, that is the
expected, confirming outcome.
