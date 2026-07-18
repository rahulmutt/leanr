#!/bin/sh
# One-time setup: clone Mathlib4 at the commit pinned in ./mathlib-pin and
# download its prebuilt .oleans via `lake exe cache get`. Network + local
# only (never run in CI). Safe to re-run: if .mathlib/ already exists we
# just fetch and re-checkout the pin instead of re-cloning.
#
# Guards against a wrong/stale pin: after checkout, the pinned Mathlib's
# lean-toolchain must byte-for-byte match ours, since Mathlib's prebuilt
# .oleans are only binary-compatible with the toolchain that built them.
set -eu

repo_root=$(cd "$(dirname "$0")/.." && pwd)
mathlib_dir="$repo_root/.mathlib"
pin_file="$repo_root/mathlib-pin"
our_toolchain_file="$repo_root/lean-toolchain"

if [ ! -f "$pin_file" ]; then
    echo "mathlib-fetch: $pin_file not found" >&2
    exit 1
fi

sha=$(sed -n '3p' "$pin_file")
if ! printf '%s' "$sha" | grep -Eq '^[0-9a-f]{40}$'; then
    echo "mathlib-fetch: line 3 of $pin_file is not a 40-hex commit SHA: '$sha'" >&2
    exit 1
fi

if [ ! -d "$mathlib_dir" ]; then
    echo "mathlib-fetch: cloning mathlib4 into $mathlib_dir ..." >&2
    git clone https://github.com/leanprover-community/mathlib4 "$mathlib_dir"
fi

cd "$mathlib_dir"
echo "mathlib-fetch: fetching and checking out $sha ..." >&2
git fetch
git checkout "$sha"

if ! cmp -s "$mathlib_dir/lean-toolchain" "$our_toolchain_file"; then
    echo "mathlib-fetch: ABORT — $mathlib_dir/lean-toolchain does not match $our_toolchain_file" >&2
    echo "mathlib-fetch: ours:    $(cat "$our_toolchain_file")" >&2
    echo "mathlib-fetch: pinned:  $(cat "$mathlib_dir/lean-toolchain")" >&2
    echo "mathlib-fetch: the SHA in $pin_file does not actually pin our toolchain — fix the pin before re-running" >&2
    exit 1
fi
echo "mathlib-fetch: toolchain match OK ($(cat "$our_toolchain_file"))" >&2

# LEANR_MATHLIB_SOURCE_ONLY=1 stops here, with the source tree checked out
# but no .oleans. That is exactly what `mise run parse:mathlib:merge` needs:
# merge decodes nothing, it only tests pass-list entries for existence on
# disk. Skipping `lake exe cache get` saves that job a 5.8GB download and
# means it needs no Lean toolchain at all (the toolchain-match check above is
# a plain `cmp` of two text files). Unset/empty keeps the full behavior.
if [ "${LEANR_MATHLIB_SOURCE_ONLY:-}" = "1" ]; then
    echo "mathlib-fetch: LEANR_MATHLIB_SOURCE_ONLY=1 — skipping \`lake exe cache get\` (sources only)." >&2
    echo "mathlib-fetch: done." >&2
    exit 0
fi

echo "mathlib-fetch: lake exe cache get ..." >&2
lake exe cache get

echo "mathlib-fetch: done." >&2
