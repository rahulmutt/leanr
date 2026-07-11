#!/bin/sh
# Run a command under an RSS ceiling. Polls /proc and SIGKILLs the whole
# process group if summed RSS exceeds <max_gib> GiB, or if the cgroup's own
# memory.current exceeds its limit minus a 2 GiB safety margin (protects the
# container even when the summed pgid RSS undercounts, e.g. processes that
# escape the pgid or allocations elsewhere in the container).
# Rust reserves large *virtual* memory, so `ulimit -v` is unusable here;
# we watch resident set instead. Exit 137 == killed for exceeding a cap.
# Known limitation: a command that allocates and exits before the first poll
# reports peak RSS 0.
set -eu

cgroup_dir="${MEM_WATCHDOG_CGROUP_DIR:-/sys/fs/cgroup}"
margin_kib=$((2 * 1024 * 1024))

max_gib="$1"; shift
max_kib=$((max_gib * 1024 * 1024))

# Clamp the requested cap to the cgroup limit (minus the safety margin), so
# the watchdog fires before the kernel OOM-killer takes the whole container.
# Leave the cap unchanged if memory.max is absent, unreadable, or "max"
# (unlimited). cgroup_cap_kib is also the memory.current kill threshold below.
cgroup_cap_kib=""
if [ -r "$cgroup_dir/memory.max" ]; then
    cgroup_limit_raw=$(cat "$cgroup_dir/memory.max" 2>/dev/null || true)
    case "$cgroup_limit_raw" in
        ''|*[!0-9]*) : ;; # absent, unreadable, or literal "max": leave unset
        *)
            cgroup_limit_kib=$((cgroup_limit_raw / 1024))
            cgroup_cap_kib=$((cgroup_limit_kib - margin_kib))
            if [ "$cgroup_cap_kib" -le 0 ]; then
                # Degenerate: the whole cgroup limit fits inside the safety
                # margin. Floor the cap at 0 (fail-safe — any resident child
                # is killed on the first poll) instead of going negative.
                cgroup_cap_kib=0
                max_kib=0
                echo "mem-watchdog: cgroup limit ${cgroup_limit_kib} kB is within the 2 GiB safety margin — effective cap 0 kB, nothing can run under this watchdog" >&2
            elif [ "$cgroup_cap_kib" -lt "$max_kib" ]; then
                max_kib=$cgroup_cap_kib
                echo "mem-watchdog: cap clamped to ${max_kib} kB (cgroup limit - 2 GiB)" >&2
            fi
            ;;
    esac
fi

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
    # Second, independent signal straight from the cgroup: catches memory the
    # pgid-RSS sum above misses (escaped processes, non-RSS charges, etc.).
    if [ -n "$cgroup_cap_kib" ] && [ -r "$cgroup_dir/memory.current" ]; then
        current_raw=$(cat "$cgroup_dir/memory.current" 2>/dev/null || true)
        case "$current_raw" in
            ''|*[!0-9]*) : ;; # absent, unreadable, or non-numeric: skip
            *)
                current_kib=$((current_raw / 1024))
                # memory.current counts reclaimable page cache ("file" in
                # memory.stat). Clean file pages are reclaimed by the kernel
                # under pressure long before the OOM-killer fires, so they
                # are not a container-death risk — subtract them, or a tree
                # of ~11k cached oleans (Mathlib) trips this kill while
                # genuine (anon) usage is far below the limit.
                file_kib=0
                if [ -r "$cgroup_dir/memory.stat" ]; then
                    file_raw=$(awk '$1=="file"{print $2; exit}' "$cgroup_dir/memory.stat" 2>/dev/null || true)
                    case "$file_raw" in
                        ''|*[!0-9]*) : ;;
                        *) file_kib=$((file_raw / 1024)) ;;
                    esac
                fi
                current_kib=$((current_kib - file_kib))
                [ "$current_kib" -lt 0 ] && current_kib=0
                if [ "$current_kib" -gt "$cgroup_cap_kib" ]; then
                    echo "mem-watchdog: memory.current - file cache ${current_kib} kB > cgroup limit - 2 GiB (${cgroup_cap_kib} kB) — killing" >&2
                    kill -KILL -"$pgid" 2>/dev/null || true
                    wait "$child" 2>/dev/null || true
                    echo "mem-watchdog: peak RSS $((peak_kib / 1024 / 1024)) GiB (${peak_kib} kB)" >&2
                    exit 137
                fi
                ;;
        esac
    fi
    sleep "${MEM_WATCHDOG_POLL_SECS:-0.25}"
done
wait "$child" || status=$?
echo "mem-watchdog: peak RSS $((peak_kib / 1024 / 1024)) GiB (${peak_kib} kB)" >&2
exit "$status"
