#!/bin/sh
# Run a command under an RSS ceiling. Polls /proc once a second and
# SIGKILLs the whole process group if summed RSS exceeds <max_gib> GiB.
# Rust reserves large *virtual* memory, so `ulimit -v` is unusable here;
# we watch resident set instead. Exit 137 == killed for exceeding the cap.
set -eu

max_gib="$1"; shift
max_kib=$((max_gib * 1024 * 1024))

setsid "$@" &
child=$!
pgid=$child

peak_kib=0
status=0
while kill -0 "$child" 2>/dev/null; do
    # Sum VmRSS (kB) across the process group.
    rss_kib=$(ps -o rss= -g "$pgid" 2>/dev/null | awk '{s+=$1} END {print s+0}')
    [ "$rss_kib" -gt "$peak_kib" ] && peak_kib=$rss_kib
    if [ "$rss_kib" -gt "$max_kib" ]; then
        echo "mem-watchdog: RSS ${rss_kib} kB > cap ${max_kib} kB — killing" >&2
        kill -KILL -"$pgid" 2>/dev/null || true
        wait "$child" 2>/dev/null || true
        echo "mem-watchdog: peak RSS $((peak_kib / 1024 / 1024)) GiB (${peak_kib} kB)" >&2
        exit 137
    fi
    sleep 1
done
wait "$child" || status=$?
echo "mem-watchdog: peak RSS $((peak_kib / 1024 / 1024)) GiB (${peak_kib} kB)" >&2
exit "$status"
