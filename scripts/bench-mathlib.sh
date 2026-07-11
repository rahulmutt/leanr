#!/bin/sh
# Benchmark leanr vs. the reference checker over the pinned Mathlib olean
# tree, on this pod. Measures wall-clock and peak RSS for each and prints a
# two-row table. This script only MEASURES — the pass bar (leanr green,
# faster than the reference, peak RSS <= 32 GiB) is asserted by whoever
# reads the output, not by this script.
#
# Reference checker: `leanchecker`. The standalone `leanprover/lean4checker`
# repo this task was originally scoped against is deprecated (see its
# README) and merged into Lean core as of v4.28.0 — it ships as the
# `leanchecker` binary inside every toolchain from that version on, so
# there is nothing to clone or build. (Confirmed: the old repo's tag list
# tops out at v4.29.0-rc8; there is no v4.32.0-rc1 tag to check out.)
# `lake env leanchecker`, run with no arguments from inside a checked-out
# Mathlib, replays every declaration of every module in the *current*
# project (i.e. every `Mathlib.*` module — its own multi-threaded mode,
# one `IO.asTask` per target module) against the environment built from its
# (trusted, not re-verified) imports. That's its best-configured,
# already-multi-threaded invocation; there is no extra flag to tune.
#
# Needs `mise run mathlib:fetch` to have completed first.
set -eu

repo_root=$(cd "$(dirname "$0")/.." && pwd)
mathlib_dir="$repo_root/.mathlib"
jobs=$(nproc)

if [ ! -d "$mathlib_dir" ]; then
    echo "bench-mathlib: $mathlib_dir not found — run \`mise run mathlib:fetch\` first" >&2
    exit 1
fi

if ! command -v /usr/bin/time >/dev/null 2>&1; then
    echo "bench-mathlib: /usr/bin/time not found on this pod (needed for the lean4checker/leanchecker row's wall-clock + peak RSS; install the 'time' package, e.g. \`apt-get install time\`)" >&2
    exit 1
fi

if ! command -v leanchecker >/dev/null 2>&1; then
    echo "bench-mathlib: 'leanchecker' not found on PATH. Since Lean v4.28.0 lean4checker ships inside the toolchain as 'leanchecker' — ensure the pinned toolchain (./lean-toolchain) is installed and active (\`mise run elan:bootstrap\`)." >&2
    exit 1
fi

work_dir=$(mktemp -d)
trap 'rm -rf "$work_dir"' EXIT

# Lake's computed LEAN_PATH for the checked-out Mathlib: its own build
# output (.mathlib/.lake/build/lib/lean) plus every dependency package's
# build output (.mathlib/.lake/packages/<dep>/.lake/build/lib/lean,
# resolved by lake — Batteries, Aesop, Qq, ImportGraph, ProofWidgets, ...)
# plus the sysroot. Both checkers below check exactly this tree.
lean_path=$(cd "$mathlib_dir" && lake env printenv LEAN_PATH)

# --- leanr -----------------------------------------------------------------
echo "bench-mathlib: running leanr (--jobs $jobs, under a 30 GiB watchdog) ..." >&2
leanr_log="$work_dir/leanr.log"
leanr_status=0
leanr_start=$(date +%s)
LEAN_PATH="$lean_path" "$repo_root/scripts/mem-watchdog.sh" 30 sh -c "
    cd '$repo_root' &&
    cargo run --release -p leanr_cli -- check --all --jobs $jobs
" >"$leanr_log" 2>&1 || leanr_status=$?
leanr_end=$(date +%s)
leanr_wall=$((leanr_end - leanr_start))
leanr_peak_gib=$(grep -o 'peak RSS [0-9]* GiB' "$leanr_log" | tail -1 | awk '{print $3}')
leanr_peak_gib=${leanr_peak_gib:-unknown}

if [ "$leanr_status" -ne 0 ]; then
    echo "bench-mathlib: leanr FAILED (exit $leanr_status) — see $leanr_log" >&2
    cp "$leanr_log" "$repo_root/bench-mathlib-leanr.log"
    echo "bench-mathlib: log copied to $repo_root/bench-mathlib-leanr.log" >&2
fi

# --- leanchecker (lean4checker, toolchain-bundled) --------------------------
echo "bench-mathlib: running leanchecker (its native multi-threaded mode) ..." >&2
leanchecker_log="$work_dir/leanchecker.log"
leanchecker_time_log="$work_dir/leanchecker.time"
leanchecker_status=0
(
    cd "$mathlib_dir" &&
    LEAN_PATH="$lean_path" /usr/bin/time -v leanchecker
) >"$leanchecker_log" 2>"$leanchecker_time_log" || leanchecker_status=$?

leanchecker_wall=$(grep 'Elapsed (wall clock) time' "$leanchecker_time_log" | sed 's/.*: //' || true)
leanchecker_peak_kib=$(grep 'Maximum resident set size' "$leanchecker_time_log" | sed 's/[^0-9]*//g' || true)
if [ -n "${leanchecker_peak_kib:-}" ]; then
    leanchecker_peak_gib=$(awk -v k="$leanchecker_peak_kib" 'BEGIN { printf "%.1f", k / 1024 / 1024 }')
else
    leanchecker_peak_gib="unknown"
fi
leanchecker_wall=${leanchecker_wall:-unknown}

if [ "$leanchecker_status" -ne 0 ]; then
    echo "bench-mathlib: leanchecker FAILED (exit $leanchecker_status) — see log below" >&2
    cat "$leanchecker_log" "$leanchecker_time_log" >&2
fi

# --- report ------------------------------------------------------------
echo
echo "checker      wall_clock       peak_rss"
echo "leanr        ${leanr_wall}s (status $leanr_status)   ${leanr_peak_gib} GiB"
echo "leanchecker  ${leanchecker_wall} (status $leanchecker_status)   ${leanchecker_peak_gib} GiB"

if [ "$leanr_status" -ne 0 ] || [ "$leanchecker_status" -ne 0 ]; then
    exit 1
fi
