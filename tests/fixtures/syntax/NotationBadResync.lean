prelude

-- M3b1 Task 8/9: an intentionally malformed `notation`/mixfix command
-- (missing the mandatory `=> term` tail) sandwiched between two good
-- commands. NO committed `.stx.jsonl` (error fixture — round-trip
-- only, per `oracle_golden.rs`'s own doc comment: a fixture without a
-- dump is excluded from oracle-equality, still checked byte-exact
-- round-trip). `⧉` is NOVEL (absent from Init — see
-- NotationMixfix.lean), though irrelevant here (never registers:
-- `derive`/`register` only ever run on a CLEAN command parse, Task 7's
-- `Ok(())` arm — this command instead takes the `Err` arm and
-- resyncs). Asserts the surrounding commands still parse (Task 9's
-- formal remit; here just the fixture + the round-trip/resync check
-- `oracle_golden.rs` already runs on every fixture).
def before := x

infixl:65 " ⧉ "

def after := x
