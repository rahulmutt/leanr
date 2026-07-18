#!/bin/bash
# MANUAL local full-sweep escape hatch: full Mathlib parse gate + pass-list
# rewrite. This is NOT the scheduled nightly — that is
# .github/workflows/nightly-sweep.yml, which shards the same work across 12
# CI jobs and gates their union. Nothing schedules this script; run it by
# hand when you have a big local box and want the unsharded sweep.
#
# It runs `mise run parse:mathlib:nightly` under the same memory watchdog pattern
# proven by the earlier ad hoc target/full_sweep_watchdog.sh scratch script
# (RAYON_NUM_THREADS=5, 27G anon-memory kill guard for a 32Gi container — an
# earlier unbounded run OOM-killed the whole container). This is the
# heavyweight/discovery tier: "what newly parses." Cost ~35h, dominated by
# per-import-set olean closure decode, not the oracle. Do NOT run this in the
# dev loop — use `mise run parse:mathlib:fast` for that (see AGENTS.md).
#
# Idempotent-safe: refuses to start a second sweep while one is already
# running. Uses an flock on a fixed lockfile rather than a pgrep-on-basename
# check — `pgrep -f "$self"` run from inside `$(...)` command substitution
# matches the substitution's OWN subshell (which inherits this script's
# cmdline), not just a genuinely concurrent invocation, so that guard always
# sees a "competitor" and NEVER lets a sweep start. flock has no such
# self-match failure class: the lock is only held by a process that actually
# holds the fd.
set -u
set -o pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo_root" || exit 1

log="$repo_root/target/nightly_sweep.log"
memlog="$repo_root/target/nightly_sweep_mem.log"
lockfile="$repo_root/target/.nightly-sweep.lock"
cgroup_memstat="/sys/fs/cgroup/memory.stat"
limit_bytes=$((27 * 1024 * 1024 * 1024)) # anon bytes; container limit is 32Gi

mkdir -p "$repo_root/target"

# The 27G guard below exists because an earlier unbounded run OOM-killed a
# 32Gi container — if the cgroup memory-stat file this guard reads isn't
# present (e.g. a host without cgroup v2 mounted the expected way), that is
# not something to silently shrug off: fail loudly at startup rather than
# run for hours with the guard quietly never arming.
if [ ! -r "$cgroup_memstat" ]; then
    echo "nightly-sweep: $cgroup_memstat not readable — the 27G memory watchdog cannot arm on \
this host; refusing to run unguarded" | tee -a "$log"
    exit 1
fi

# Refuse to start if another sweep is already running — one sweep at a
# time, so a stray re-run (or a leftover background sweep) can't stack two ~35h jobs and
# double the memory pressure.
exec 9>"$lockfile"
if ! flock -n 9; then
    echo "nightly-sweep: another sweep is already running (lock held on $lockfile) — refusing to \
start a second sweep" | tee -a "$log"
    exit 1
fi

echo "[nightly-sweep] launch $(date -u +%FT%TZ) RAYON_NUM_THREADS=5" | tee -a "$log" >>"$memlog"
setsid env RAYON_NUM_THREADS=5 mise run parse:mathlib:nightly >>"$log" 2>&1 &
pid=$!
pgid=$(ps -o pgid= -p "$pid" | tr -d ' ')

while kill -0 "$pid" 2>/dev/null; do
    anon=$(awk '$1=="anon"{print $2}' "$cgroup_memstat")
    echo "$(date +%s) anon=$anon" >>"$memlog"
    if [ -n "$anon" ] && [ "$anon" -gt "$limit_bytes" ]; then
        echo "[nightly-sweep] BREACH anon=$anon > $limit_bytes — killing sweep pgid $pgid $(date -u +%FT%TZ)" | tee -a "$log" >>"$memlog"
        kill -TERM -- "-$pgid"
        sleep 15
        kill -KILL -- "-$pgid" 2>/dev/null
        echo "WATCHDOG_KILLED" >>"$log"
        exit 42
    fi
    sleep 5
done
wait "$pid"
rc=$?
echo "[nightly-sweep] sweep exited rc=$rc $(date -u +%FT%TZ)" >>"$memlog"
echo "SWEEP_EXIT rc=$rc" >>"$log"
exit "$rc"
