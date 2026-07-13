#!/bin/sh
# M2b acceptance (spec §Testing): fresh clone of pinned Mathlib, isolated
# XDG cache, bare `leanr build` of the full closure; every artifact
# byte-diffed against the lake-built artifacts in .mathlib. Hours of
# compute; network (dependency clones from GitHub); local only, never CI.
# Needs: mathlib:fetch done (lake-built artifacts present), elan toolchain.
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

export XDG_CACHE_HOME="$tmp/xdg"
echo "acceptance: leanr build (full closure — this takes hours) ..." >&2
start=$(date +%s)
(cd "$tmp/mathlib" && "$leanr" build)
end=$(date +%s)
echo "acceptance: build wall time ${start}..${end}: $((end - start))s" >&2

echo "acceptance: byte-diffing artifacts against .mathlib ..." >&2
# Divergence policy (docs/superpowers/specs/2026-07-12-m2b-acceptance-divergence-investigation.md):
# a full-Mathlib acceptance run found 22/42,820 artifacts differing from
# lake's, confined to *.ilean and *.olean.private on 12 modules. Investigation
# (same doc) reproduced this using lake alone: back-to-back lake rebuilds of
# the same source agree with each other but not with the pre-existing oracle
# for these two artifact kinds — verdict BENIGN, lake's own cross-session
# byte-nondeterminism (thread-scheduling-dependent reference-tracking
# metadata), not a leanr defect. .olean/.ir/.olean.server are never affected.
# The investigation only established benign cause for CONTENT variance in
# artifacts present on both sides — an artifact leanr produced that the
# oracle lacks entirely is not covered by that verdict and is never excused.
# So: every artifact is still diffed, but mismatches are split into a
# deterministic-kind list (must be empty) and a known-nondeterministic-kind
# list (reported, non-blocking). Only a content diff on an artifact present
# on both sides, of kind *.ilean / *.olean.private, lands in the
# known-nondeterministic list; a missing-on-oracle-side artifact always
# lands in the deterministic (hard-fail) list, regardless of extension.
mismatches="$tmp/mismatches.txt"; : > "$mismatches"
deterministic_mismatches="$tmp/deterministic_mismatches.txt"; : > "$deterministic_mismatches"
nondeterministic_mismatches="$tmp/nondeterministic_mismatches.txt"; : > "$nondeterministic_mismatches"
total_file="$tmp/count.txt"; echo 0 > "$total_file"
for pkg_dir in "$tmp/mathlib/.leanr/build"/*/; do
    pkg=$(basename "$pkg_dir")
    if [ "$pkg" = mathlib ]; then
        oracle="$repo_root/.mathlib/.lake/build/lib/lean"
    else
        oracle="$repo_root/.mathlib/.lake/packages/$pkg/.lake/build/lib/lean"
    fi
    [ -d "$pkg_dir/lib" ] || continue
    (cd "$pkg_dir/lib" && find . -type f | sort) | while IFS= read -r f; do
        echo $(($(cat "$total_file") + 1)) > "$total_file"
        if [ ! -e "$oracle/$f" ]; then
            # Present on the leanr side, entirely absent on the oracle side:
            # never excusable, regardless of extension — the divergence
            # investigation only covers content variance in artifacts
            # present on both sides.
            echo "$pkg/$f (missing on oracle side)" >> "$mismatches"
            echo "$pkg/$f (missing on oracle side)" >> "$deterministic_mismatches"
        elif ! cmp -s "$pkg_dir/lib/$f" "$oracle/$f"; then
            echo "$pkg/$f" >> "$mismatches"
            case "$f" in
                *.ilean|*.olean.private) echo "$pkg/$f" >> "$nondeterministic_mismatches" ;;
                *) echo "$pkg/$f" >> "$deterministic_mismatches" ;;
            esac
        fi
    done
done
count=$(cat "$total_file")
if [ -s "$deterministic_mismatches" ]; then
    echo "acceptance: FAIL — $(wc -l < "$mismatches") of $count artifacts differ:" >&2
    head -50 "$mismatches" >&2
    exit 1
fi
if [ -s "$nondeterministic_mismatches" ]; then
    n=$(wc -l < "$nondeterministic_mismatches")
    byte_identical_count=$((count - n))
    echo "acceptance: byte-diff PASS — $byte_identical_count artifacts byte-identical to lake's; $n known-nondeterministic divergences (.ilean/.olean.private, both sides present — see M2b spec §Acceptance)" >&2
    cat "$nondeterministic_mismatches" >&2
else
    echo "acceptance: byte-diff PASS — $count artifacts byte-identical to lake's" >&2
fi
echo "acceptance: record wall time, --jobs (default nproc), and module count in the M2b spec" >&2

# --- M2c: warm cache hit, incremental cone, store integrity (spec
# §Acceptance items 2-4) --------------------------------------------------
# Same clone, same $XDG_CACHE_HOME populated by the cold build above; no
# `leanr clean` between steps (the CAS is what should make the rebuilds
# cheap/scoped, not a fresh checkout).

echo "acceptance: warm rebuild (same clone + XDG cache; expect a full cache hit, zero lean runs) ..." >&2
warm_out="$tmp/warm-build.txt"
(cd "$tmp/mathlib" && "$leanr" build) > "$warm_out"
if ! grep -q '^built 0 modules (' "$warm_out"; then
    echo "acceptance: FAIL — warm build ran lean (expected \"built 0 modules (N cached)\"):" >&2
    tail -5 "$warm_out" >&2
    exit 1
fi
warm_stale=$(grep '^\[' "$warm_out" | grep -vc ' (cached) (' || true)
if [ "$warm_stale" -ne 0 ]; then
    echo "acceptance: FAIL — warm build had $warm_stale module(s) without the \"(cached)\" tag:" >&2
    grep '^\[' "$warm_out" | grep -v ' (cached) (' >&2
    exit 1
fi
echo "acceptance: PASS — $(grep '^built ' "$warm_out")" >&2

echo "acceptance: incremental rebuild — locating an editable leaf module (zero in-workspace dependents) ..." >&2
# The root ("mathlib") package's build-plan waves are a topological sort
# (wave = 1 + max(dependency waves)), and `print_json_plan` emits modules
# in ascending wave order — so the LAST "mathlib"-package entry in the
# plan sits in that package's maximum wave, which by construction has no
# in-workspace dependent (a dependent would need a strictly later wave,
# and none exists). Editing that module's source therefore has a
# downstream cone of exactly {itself}: the simplest, unambiguous instance
# of the "edit one leaf, assert only its cone rebuilds" property. Broader
# multi-module cone propagation (a leaf with real dependents, a toggled
# leanOption, a bumped toolchain/leanr version, a moved git-dep rev) is
# already exhaustively covered by the hermetic `cache:incremental` gate
# (`mise run cache:incremental`, wired into `ci`) — this acceptance run's
# job is an end-to-end sanity check against the real Mathlib closure, not
# a restatement of that harness.
plan_json="$tmp/plan.json"
(cd "$tmp/mathlib" && "$leanr" build --dry-run --json) > "$plan_json"
leaf_name=$(awk '
    /"name":/    { gsub(/^ *"name": "/, ""); gsub(/"[,]?$/, ""); pending_name = $0 }
    /"package":/ { gsub(/^ *"package": "/, ""); gsub(/"[,]?$/, ""); pending_pkg = $0 }
    /"file":/    { if (pending_pkg == "mathlib") { leaf_name = pending_name } }
    END { print leaf_name }
' "$plan_json")
leaf_file=$(awk '
    /"name":/    { gsub(/^ *"name": "/, ""); gsub(/"[,]?$/, ""); pending_name = $0 }
    /"package":/ { gsub(/^ *"package": "/, ""); gsub(/"[,]?$/, ""); pending_pkg = $0 }
    /"file":/    {
        gsub(/^ *"file": "/, ""); gsub(/"[,]?$/, "")
        if (pending_pkg == "mathlib") { leaf_file = $0 }
    }
    END { print leaf_file }
' "$plan_json")
if [ -z "$leaf_name" ] || [ -z "$leaf_file" ]; then
    echo "acceptance: FAIL — could not find a \"mathlib\"-package module in $plan_json" >&2
    exit 1
fi
echo "acceptance: editing leaf module $leaf_name ($leaf_file) ..." >&2
printf '\n-- acceptance: M2c incremental-cache probe (%s)\n' "$(date +%s)" >> "$tmp/mathlib/$leaf_file"

incr_out="$tmp/incremental-build.txt"
(cd "$tmp/mathlib" && "$leanr" build) > "$incr_out"
stale_lines="$tmp/incremental-stale.txt"
grep '^\[' "$incr_out" | grep -v ' (cached) (' > "$stale_lines" || true
stale_count=$(wc -l < "$stale_lines")
if [ "$stale_count" -ne 1 ]; then
    echo "acceptance: FAIL — incremental rebuild reported $stale_count non-cached module(s), expected exactly 1 ($leaf_name):" >&2
    cat "$stale_lines" >&2
    exit 1
fi
stale_module=$(sed -E 's/^\[[0-9]+\/[0-9]+\] ([^ ]+) \([0-9.]+s\)$/\1/' "$stale_lines")
if [ "$stale_module" != "$leaf_name" ]; then
    echo "acceptance: FAIL — the single non-cached module was \"$stale_module\", not the edited leaf \"$leaf_name\":" >&2
    cat "$stale_lines" >&2
    exit 1
fi
echo "acceptance: PASS — incremental rebuild recompiled exactly the edited leaf ($leaf_name); every other module stayed cached" >&2

echo "acceptance: cache integrity (blob bytes == content key; no dangling manifests) ..." >&2
verify_out="$tmp/cache-verify.txt"
if ! "$leanr" cache verify > "$verify_out" 2>&1; then
    echo "acceptance: FAIL — leanr cache verify exited non-zero:" >&2
    cat "$verify_out" >&2
    exit 1
fi
if ! grep -q '^cache verify: OK (' "$verify_out"; then
    echo "acceptance: FAIL — unexpected \`leanr cache verify\` output:" >&2
    cat "$verify_out" >&2
    exit 1
fi
echo "acceptance: PASS — $(cat "$verify_out")" >&2

echo "acceptance: PASS — cold byte-diff, warm cache-hit, incremental cone, and store integrity all verified" >&2
