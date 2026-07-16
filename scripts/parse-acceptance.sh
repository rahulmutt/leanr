#!/usr/bin/env bash
# M3a acceptance (spec §Acceptance): regenerate oracle dumps FRESH from
# the pinned toolchain, diff against committed dumps (catches stale
# fixtures), then run the full hermetic gate + fuzz smoke. Local-only
# (needs the toolchain), like build:acceptance.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== [1/4] fresh oracle dumps vs committed =="
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

echo "== [2/4] hermetic golden + property gates =="
cargo test --release -p leanr_syntax

echo "== [3/4] leanr parse --dump == oracle, per fixture =="
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

echo "== [4/4] fuzz smoke (60s) =="
mise run fuzz:syntax

echo "M3a acceptance: ALL GREEN"
