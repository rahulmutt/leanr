#!/usr/bin/env bash
# M3a acceptance (spec §Acceptance): regenerate oracle dumps FRESH from
# the pinned toolchain, diff against committed dumps (catches stale
# fixtures), then run the full hermetic gate + fuzz smoke. Local-only
# (needs the toolchain), like build:acceptance.
#
# M3b2a Task 10 extends this with a step [5/5] covering the import
# corpus (tests/fixtures/syntax/import/) the same way, since the flat
# fixture dir [1]/[3] loops above never touch it.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== [1/5] fresh oracle dumps vs committed =="
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
for f in tests/fixtures/syntax/*.lean; do
  base=$(basename "$f")
  [ "$base" = dump_syntax.lean ] && continue
  [ "$base" = dump_syntax_elab.lean ] && continue
  committed="${f%.lean}.stx.jsonl"
  [ -f "$committed" ] || { echo "  (no dump — round-trip-only) $base"; continue; }
  # M3b1 same-file notation fixtures (Notation*.lean) grow their own
  # grammar mid-file — only observable by actually ELABORATING each
  # command, which the parse-only dump_syntax.lean can't do (see its
  # own header comment and dump_syntax_elab.lean's module doc). Use the
  # elaborating dumper for those, same as `fixtures:regen-notation`.
  case "$base" in
    Notation*.lean) dumper=tests/fixtures/syntax/dump_syntax_elab.lean ;;
    *) dumper=tests/fixtures/syntax/dump_syntax.lean ;;
  esac
  lean --run "$dumper" "$f" > "$tmp/$base.jsonl"
  diff -u "$committed" "$tmp/$base.jsonl" || { echo "STALE DUMP: $f"; exit 1; }
  echo "  ok $base"
done

echo "== [2/5] hermetic golden + property gates =="
cargo test --release -p leanr_syntax

echo "== [3/5] leanr parse --dump == oracle, per fixture =="
cargo build --release -p leanr_cli
for f in tests/fixtures/syntax/*.lean; do
  base=$(basename "$f")
  [ "$base" = dump_syntax.lean ] && continue
  [ "$base" = dump_syntax_elab.lean ] && continue
  committed="${f%.lean}.stx.jsonl"
  [ -f "$committed" ] || continue
  ./target/release/leanr parse --dump "$f" | diff -u "$committed" - \
    || { echo "CLI DUMP DIVERGES: $f"; exit 1; }
  echo "  ok $base"
done

echo "== [4/5] fuzz smoke (60s) =="
mise run fuzz:syntax

# M3b2a Task 10: steps [1]/[3] above only iterate the flat fixture dir
# (tests/fixtures/syntax/*.lean); the import corpus
# (tests/fixtures/syntax/import/) needs its own fresh-dump + CLI-dump
# checks, same commands as the `fixtures:regen` Task 2 import lines
# (mise.toml) — including the `rm -f Init.olean` first / stub rebuild
# last invariant documented there (a committed stub Init.olean shadows
# the real Init's submodules once LEAN_PATH=$PWD is set, breaking every
# importer dump).
echo "== [5/5] import corpus: fresh oracle dumps + CLI dump vs committed =="
(
  cd tests/fixtures/syntax/import
  rm -f Init.olean
  lean NotaDep.lean -o NotaDep.olean
  lean NotaDepMeta.lean -o NotaDepMeta.olean
  tmp2=$(mktemp -d)
  trap 'rm -rf "$tmp2"' EXIT
  for f in ImportMixfix ImportMunch ImportCat; do
    LEAN_PATH="$PWD" lean --run ../dump_syntax.lean "$f.lean" > "$tmp2/$f.stx.jsonl"
    diff -u "$f.stx.jsonl" "$tmp2/$f.stx.jsonl" || { echo "STALE IMPORT DUMP: $f"; exit 1; }
    echo "  ok $f"
  done
  LEAN_PATH="$PWD" lean --run ../dump_syntax_elab.lean ImportOverload.lean > "$tmp2/ImportOverload.stx.jsonl"
  diff -u ImportOverload.stx.jsonl "$tmp2/ImportOverload.stx.jsonl" \
    || { echo "STALE IMPORT DUMP: ImportOverload"; exit 1; }
  echo "  ok ImportOverload"
  lean Init.lean -o Init.olean
)
for f in tests/fixtures/syntax/import/Import*.lean; do
  base=$(basename "$f")
  committed="${f%.lean}.stx.jsonl"
  env -u LEAN_PATH ./target/release/leanr parse --dump --path tests/fixtures/syntax/import "$f" \
    | diff -u "$committed" - \
    || { echo "CLI DUMP DIVERGES: $f"; exit 1; }
  echo "  ok $base"
done

echo "M3b2a acceptance: ALL GREEN"
