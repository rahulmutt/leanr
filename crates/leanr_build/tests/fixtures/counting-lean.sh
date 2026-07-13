#!/bin/sh
# Test double for the M2c staleness-correctness harness
# (cache_incremental.rs). Mirrors fake-lean.sh's -o/-i/--setup arg
# parsing and artifact-family emission VERBATIM; the only additions are:
#   (a) logging the invocation's source path to $COUNTING_LEAN_LOG, so
#       the harness can assert exactly which modules re-ran, and
#   (b) making each artifact's bytes a function of the source file's
#       CONTENTS (not just its path), so editing a .lean file's text
#       actually changes its olean/ilean bytes -> changes its
#       fingerprint -> (via Merkle recursion) its dependents' -> they
#       rebuild. A fake lean that emitted constant bytes could pass the
#       harness for the wrong reason (see task-9 brief, non-vacuity note).
set -eu
src=""; o=""; i=""; setup=""
while [ $# -gt 0 ]; do
  case "$1" in
    -o) o="$2"; shift 2 ;;
    -i) i="$2"; shift 2 ;;
    --setup) setup="$2"; shift 2 ;;
    --json) shift ;;
    +*) shift ;;
    -*) shift ;;
    *) src="$1"; shift ;;
  esac
done
: "${COUNTING_LEAN_LOG:=/dev/null}"
printf '%s\n' "$src" >> "$COUNTING_LEAN_LOG"
[ -f "$setup" ] || { echo "counting-lean: missing setup file $setup" >&2; exit 3; }
mkdir -p "$(dirname "$o")" "$(dirname "$i")"
printf 'olean:%s:' "$src" > "$o"
cat "$src" >> "$o"
printf 'ilean:%s:' "$src" > "$i"
cat "$src" >> "$i"
exit 0
