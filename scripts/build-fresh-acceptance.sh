#!/bin/sh
# M2a acceptance (spec §Testing): a fresh clone of pinned Mathlib —
# no .lake/, lake never run by the user — resolves via
# `leanr build --dry-run --json` byte-identically to the
# pre-materialized .mathlib checkout. Network (dependency clones from
# GitHub); local only, never CI. Needs: mathlib:fetch done, elan
# toolchain installed.
set -eu

repo_root=$(cd "$(dirname "$0")/.." && pwd)
sha=$(sed -n '3p' "$repo_root/mathlib-pin")
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT INT TERM

echo "acceptance: building leanr ..." >&2
cargo build --release -p leanr_cli
leanr="$repo_root/target/release/leanr"

echo "acceptance: fresh clone at $sha (tracked files only — no .lake) ..." >&2
git clone -q "$repo_root/.mathlib" "$tmp/mathlib"
git -C "$tmp/mathlib" -c advice.detachedHead=false checkout -q --detach "$sha"
test ! -e "$tmp/mathlib/.lake" || { echo "clone unexpectedly has .lake" >&2; exit 1; }

echo "acceptance: resolving the fresh clone (fetches deps from GitHub) ..." >&2
(cd "$tmp/mathlib" && "$leanr" build --dry-run --json) > "$tmp/fresh.json"

echo "acceptance: resolving the pre-materialized checkout ..." >&2
(cd "$repo_root/.mathlib" && "$leanr" build --dry-run --json) > "$tmp/base.json"

if ! diff -q "$tmp/fresh.json" "$tmp/base.json" >/dev/null; then
    echo "acceptance: FAIL — fresh-clone plan differs from baseline:" >&2
    diff "$tmp/fresh.json" "$tmp/base.json" | head -50 >&2
    exit 1
fi

modules=$(grep -c '"wave"' "$tmp/fresh.json")
packages=$(grep -c '"rev"' "$tmp/fresh.json")
echo "acceptance: PASS — plans identical; $packages packages, $modules modules" >&2
echo "acceptance: record these numbers in the M2a spec's Acceptance section" >&2
