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
# So: every artifact is still diffed, but mismatches are split into a
# deterministic-kind list (must be empty) and a known-nondeterministic-kind
# list (*.ilean / *.olean.private — reported, non-blocking).
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
        if ! cmp -s "$pkg_dir/lib/$f" "$oracle/$f"; then
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
    deterministic_count=$((count - n))
    echo "acceptance: PASS — $deterministic_count deterministic artifacts byte-identical to lake's; $n known-nondeterministic divergences (.ilean/.olean.private — see M2b spec §Acceptance)" >&2
    cat "$nondeterministic_mismatches" >&2
    exit 0
fi
echo "acceptance: PASS — $count artifacts byte-identical to lake's" >&2
echo "acceptance: record wall time, --jobs (default nproc), and module count in the M2b spec" >&2
