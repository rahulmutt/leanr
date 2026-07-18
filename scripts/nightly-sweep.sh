#!/bin/bash
# Nightly discovery sweep: full Mathlib parse gate + pass-list rewrite
# (`mise run parse:mathlib:nightly`), under the same memory watchdog pattern
# proven by the earlier ad hoc target/full_sweep_watchdog.sh scratch script
# (RAYON_NUM_THREADS=5, 27G anon-memory kill guard for a 32Gi container — an
# earlier unbounded run OOM-killed the whole container). This is the
# heavyweight/discovery tier: "what newly parses." Cost ~35h, dominated by
# per-import-set olean closure decode, not the oracle. Do NOT run this in the
# dev loop — use `mise run parse:mathlib:fast` for that (see AGENTS.md).
#
# Idempotent-safe: refuses to start a second sweep while one is already
# running (pgrep on this script's own basename).
set -u

repo_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo_root" || exit 1

log="$repo_root/target/nightly_sweep.log"
memlog="$repo_root/target/nightly_sweep_mem.log"
limit_bytes=$((27 * 1024 * 1024 * 1024)) # anon bytes; container limit is 32Gi
self="$(basename "$0")"

mkdir -p "$repo_root/target"

# Refuse to start if another sweep (this script, under any invocation) is
# already running — one sweep at a time, so a cron misfire or a manual
# re-run can't stack two ~35h jobs and double the memory pressure.
other_pids=$(pgrep -f "$self" | grep -v "^$$\$" || true)
if [ -n "$other_pids" ]; then
    echo "nightly-sweep: already running (pid(s): $other_pids) — refusing to start a second sweep" | tee -a "$log"
    exit 1
fi

echo "[nightly-sweep] launch $(date -u +%FT%TZ) RAYON_NUM_THREADS=5" | tee -a "$log" >>"$memlog"
setsid env RAYON_NUM_THREADS=5 mise run parse:mathlib:nightly >>"$log" 2>&1 &
pid=$!
pgid=$(ps -o pgid= -p "$pid" | tr -d ' ')

while kill -0 "$pid" 2>/dev/null; do
    anon=$(awk '$1=="anon"{print $2}' /sys/fs/cgroup/memory.stat 2>/dev/null)
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
