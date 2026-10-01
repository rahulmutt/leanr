# `setElabConfig` — design spec

## Where this sits

M4b-4 is complete (#49–#55), and its HIGH follow-up, the
`instantiateBetaRevRange` nested-redex gap, closed in #56. This spec
takes follow-up (2) from `2026-10-01-m4b4c-elab-as-elim-design.md`
§ Landed › P2 (T6-D): leanr's `TermElabM` runs under
`Config::default()`, but the oracle elaborates under `setElabConfig`.
Because of that gap leanr rejects `Eq.ndrec p h`, a term the oracle
accepts. Follow-up (3), `fun.rs` `expandFunBinders`, is out of scope.

Pinned oracle: `leanprover/lean4:v4.33.0-rc1`. The pin is not bumped.
Both citations below were opened while writing this spec:

- `src/lean/Lean/Elab/Config.lean:61-62`:
  `def setElabConfig (cfg : Meta.Config) : Meta.Config :=
  { cfg with foApprox := true, ctxApprox := true, constApprox := false,
  quasiPatternApprox := false }`
- `src/lean/Lean/Elab/Term/TermElabM.lean:2226-2227`:
  `def TermElabM.run … := withConfig setElabConfig (x ctx |>.run s)`

## Evidence

The results below were run, not read. The scratch harness lives in
`target/approx-probe/` and is uncommitted.

**The corpus does not depend on either flag.** `dump_elab.lean` was
copied and each elaboration wrapped in
`Lean.Meta.withConfig (fun c => { c with F := false })`. The run was
done once with `F = ctxApprox` and once with `F = foApprox`. Each
output was then diffed against the committed
`tests/fixtures/elab/elab-queries.jsonl` (331 records). **Neither run
changed a single record.** `p5/propagate-short`'s "internal exception
#3" on stderr is pre-existing: the committed corpus has 331 lines too.

**leanr does not regress with the flags on.** `oracle_elab.rs` was
temporarily changed to build its `MetaCtx` with `fo_approx: true,
ctx_approx: true`. `oracle_elab_gate` stays green on all 331 records.
The edit was reverted.

**`foApprox` matters, and `ctxApprox` was not observed to.** Eight
candidate terms were elaborated under `import Init`, each with the flag
on and then off:

| Term | `foApprox` off | `ctxApprox` off |
|---|---|---|
| `fun (a : Nat) (p : a = a) (h : a = a) => Eq.ndrec p h` | **rejected**: "Application type mismatch" (on: `h ▸ p`) | same as on |
| 7 higher-order / `▸` / `∃`-intro / nested-binder candidates | same as on | same as on |

**Consequence.** Turning on `foApprox` is the fix. `ctxApprox` is set
so that the config matches the oracle's, but it stays inert in leanr.
Its rescue lives in the oracle's slow, term-rewriting
`CheckAssignment.checkAssignmentAux` (`ExprDefEq.lean:952-978`), which
leanr does not port: `assign.rs`'s `check_assignment_scope` names it as
a SEAM. No probe found a term where the rescue matters, so the port is
deferred until a term that needs it shows up.

## Design

### Where the config is set

**`TermElabM::new` applies `set_elab_config` to the `MetaCtx` it
takes.** The oracle wraps the whole `TermElabM` run in `withConfig`,
and leanr's `TermElabM` owns its `MetaCtx` for its whole lifetime, so
setting the config at construction is equivalent. It also leaves no
caller able to forget it.

Every leanr path into elaboration goes through `TermElabM::new`: the
`oracle_elab.rs` / `binder_smoke.rs` / `tests/support` harnesses, and
the `#[cfg(test)]` fixtures in `head.rs`, `elim_info.rs` and `fun.rs`.
No production code calls `MetaCtx::new` for elaboration. The oracle
reaches `getElabElimInfo` and everything else under `TermElabM.run`, so
no elaboration site should keep the default `Meta.Config`.

Two approaches were rejected:

- **Callers pass the elab config.** That means five or more call sites
  that can drift, and nothing makes a new one pick the right value.
- **Changing `Config::default()`.** `leanr_meta`'s tests and `synth.rs`
  rely on the oracle's `Meta.Config` defaults, where both flags are off.

### Components

- **`leanr_elab`: `set_elab_config(Config) -> Config`.** A pure function
  that transcribes `Config.lean:61-62`. It sets `fo_approx`,
  `ctx_approx`, `const_approx := false` and
  `quasi_pattern_approx := false`, and leaves every other field
  untouched. It cites the oracle.
- **`leanr_meta`: an additive `MetaCtx::set_config(Config)` accessor**,
  next to the existing `cfg()`/`set_transparency`. This uses the precedent that
  `leanr_meta/src` may gain TCB-neutral accessors `leanr_elab` needs.
  The defeq cache key is derived from the whole `Config`, so switching
  configs cannot leak cached results (`config.rs` module doc).
- **`TermElabM::new`** calls `mctx.set_config(set_elab_config(mctx.cfg()))`.
- **`assign.rs` `ctxApprox` SEAM doc.** Updated to record that
  `ctx_approx` is now on during elaboration but still inert, with this
  spec's probe as the evidence and the slow-path port as the open
  follow-up.

### Data flow and interactions

- `with_full_approx_def_eq` (`elim.rs:326`) still raises
  `quasi_pattern_approx` and `const_approx` on top of the elab config,
  and still restores to the elab config, as the oracle does.
- `synth.rs` sets its own instance-synthesis config, so it is
  unaffected.
- The scopes `with_transparency` and `with_assignable_synthetic_opaque`
  save and restore the whole `cfg` or a single field. Each should be
  checked to confirm it restores to the elab config and not to
  `Config::default()`.

### Error handling

There are no new error paths. Terms that used to fail with a
unification or type-mismatch error may now succeed, which is the point
of the change. A full corpus rerun shows no existing record changes.

## Testing

- **New corpus records**, generated by the oracle via
  `mise run fixtures:regen-elab`:
  - `elim/ndrec`: `fun (a : Nat) (p : Eq a a) (h : Eq a a) => Eq.ndrec p h`,
    respelled for `Elab0` if it lacks `=` notation. This reinstates the
    record that T6-D dropped, and drops the `dump_elab.lean:1138-1140`
    comment that explains the drop.
  - One more `foApprox`-dependent term on a non-eliminator path. It is
    found at plan time and must be **shown, by an oracle run with
    `foApprox := false`, to flip** (a candidate list is not evidence).
- **Discrimination, required.** With `TermElabM::new`'s
  `set_config` call removed, both new records must fail `oracle_elab_gate`.
  Run that mutation and record its result. Run a second mutation as
  well: `set_elab_config` sets only `ctx_approx`. That one must also
  turn the records red.
- **A unit test of `set_elab_config`** pins all four fields and checks
  that the rest of the config passes through unchanged.
- **Full `mise run ci`** must be green. Run `cargo fmt` before
  committing.

## Out of scope

- Porting `CheckAssignment.checkAssignmentAux` and the `ctxApprox`
  rescue, until a term needing it is found.
- `fun.rs` `expandFunBinders` (follow-up 3).
- The other M4b-4c coverage follow-ups (`preElim2`, two-extra-argument
  over-application, `[inst]` eliminator, `check_proj` test).

## Landed

(filled in when the PR merges)
