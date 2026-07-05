-- A `module`-mode, `prelude` fixture for multi-region olean decoding
-- (M1b Task 13a). `module` makes the compiler emit companion parts:
-- `ModPriv.olean` (public interface), `ModPriv.olean.server`, and
-- `ModPriv.olean.private` (the FULL constant set). `prelude` suppresses
-- the implicit `import Init`, so the module imports nothing and the whole
-- merged constant set replays from an empty kernel environment (hermetic;
-- see crates/leanr_olean/tests/check_fixtures.rs).
--
-- The point of the fixture: `secret` is `private`, so it lives ONLY in the
-- `.olean.private` part as `_private.ModPriv.0.secret`, and the public
-- `bump` references it. In the base `.olean`, `bump`/`triv` are stored as
-- bare `axiom` stubs (bodies not exported); only the `.private` part has
-- their checkable `def`/`thm` bodies. Decoding all parts together and
-- preferring the private versions is exactly what lets `_private.*`
-- helpers resolve during replay.
module

prelude

public inductive N where
  | zero : N
  | succ : N → N

private def secret (n : N) : N := N.succ n

public def bump (n : N) : N := secret n

public inductive Truth : Prop where
  | intro : Truth

public theorem triv : Truth := Truth.intro
