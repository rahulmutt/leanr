#!/bin/sh
# M2d acceptance (spec §Testing, recorded run): cold-build pinned Mathlib
# on "machine A" (fresh clone, isolated XDG), push the CAS to a local
# static server, then build on "machine B" (fresh clone, EMPTY XDG,
# --remote) — expect ~zero lean invocations, all modules downloaded, and
# STRICT byte-identity between A's and B's artifacts (A↔lake fidelity is
# scripts/build-fresh-acceptance.sh's standing gate). Finally exercise
# `cache get` on an empty "machine C" XDG. Hours of compute; local only.
# Needs: mathlib:fetch done, elan toolchain.
set -eu

repo_root=$(cd "$(dirname "$0")/.." && pwd)
sha=$(sed -n '3p' "$repo_root/mathlib-pin")
tmp=$(mktemp -d)
server_pid=""
trap 'if [ -n "$server_pid" ]; then kill "$server_pid" 2>/dev/null || true; fi; rm -rf "$tmp"' EXIT INT TERM

echo "acceptance: building leanr + cas_httpd ..." >&2
cargo build --release -p leanr_cli
cargo build --release -p leanr_build --example cas_httpd
leanr="$repo_root/target/release/leanr"
cas_httpd="$repo_root/target/release/examples/cas_httpd"

clone() { # $1 = dest
    git clone -q "$repo_root/.mathlib" "$1"
    git -C "$1" -c advice.detachedHead=false checkout -q --detach "$sha"
}

# --- Machine A: cold build ------------------------------------------------
clone "$tmp/a"
export XDG_CACHE_HOME="$tmp/xdg-a"
echo "acceptance: machine A cold build (hours) ..." >&2
(cd "$tmp/a" && "$leanr" build)

# --- Serve + push ----------------------------------------------------------
served="$tmp/served"; mkdir -p "$served/cas"
"$cas_httpd" "$served" > "$tmp/addr.txt" &
server_pid=$!
sleep 1
addr=$(cat "$tmp/addr.txt")
echo "acceptance: cas_httpd at $addr" >&2

echo "acceptance: cache push (machine A -> local S3 stand-in) ..." >&2
push_out="$tmp/push.txt"
start=$(date +%s)
(cd "$tmp/a" && \
    AWS_ENDPOINT_URL="http://$addr" AWS_ACCESS_KEY_ID=acceptance \
    AWS_SECRET_ACCESS_KEY=acceptance \
    "$leanr" cache push --to s3://cas) | tee "$push_out"
end=$(date +%s)
echo "acceptance: push wall time $((end - start))s" >&2
grep -q '^cache push: ' "$push_out" || { echo "FAIL: no push summary" >&2; exit 1; }

# --- Machine B: fresh XDG, remote-only build --------------------------------
clone "$tmp/b"
export XDG_CACHE_HOME="$tmp/xdg-b"
echo "acceptance: machine B build --remote (expect zero lean runs) ..." >&2
b_out="$tmp/b-build.txt"
start=$(date +%s)
(cd "$tmp/b" && "$leanr" build --remote "http://$addr/cas") > "$b_out"
end=$(date +%s)
echo "acceptance: machine B wall time $((end - start))s" >&2
if ! grep -q '^built 0 modules (' "$b_out"; then
    echo "acceptance: FAIL — machine B ran lean:" >&2
    tail -5 "$b_out" >&2
    exit 1
fi
not_downloaded=$(grep '^\[' "$b_out" | grep -vc ' (downloaded) (' || true)
if [ "$not_downloaded" -ne 0 ]; then
    echo "acceptance: FAIL — $not_downloaded module(s) not tagged (downloaded):" >&2
    grep '^\[' "$b_out" | grep -v ' (downloaded) (' | head -20 >&2
    exit 1
fi
echo "acceptance: PASS — $(grep '^built ' "$b_out")" >&2

echo "acceptance: strict A<->B artifact byte-diff ..." >&2
mismatches="$tmp/ab-mismatches.txt"; : > "$mismatches"
count=0
(cd "$tmp/a/.leanr/build" && find . -type f -path '*/lib/*' | sort) | while IFS= read -r f; do
    cmp -s "$tmp/a/.leanr/build/$f" "$tmp/b/.leanr/build/$f" || echo "$f" >> "$mismatches"
done
count=$(cd "$tmp/a/.leanr/build" && find . -type f -path '*/lib/*' | wc -l)
if [ -s "$mismatches" ]; then
    echo "acceptance: FAIL — $(wc -l < "$mismatches") of $count artifacts differ A<->B:" >&2
    head -50 "$mismatches" >&2
    exit 1
fi
echo "acceptance: PASS — $count artifacts byte-identical A<->B (A<->lake is build-fresh-acceptance.sh's standing gate)" >&2

echo "acceptance: machine B cache verify ..." >&2
"$leanr" cache verify | grep -q '^cache verify: OK (' || { echo "FAIL: cache verify" >&2; exit 1; }
echo "acceptance: PASS — machine B store integrity clean" >&2

# --- Machine C: explicit prefetch ------------------------------------------
clone "$tmp/c"
export XDG_CACHE_HOME="$tmp/xdg-c"
echo "acceptance: machine C cache get (explicit prefetch) ..." >&2
get_out="$tmp/get.txt"
(cd "$tmp/c" && "$leanr" cache get --remote "http://$addr/cas") | tee "$get_out"
grep -q ' 0 failed$' "$get_out" || { echo "FAIL: cache get had failures" >&2; exit 1; }
c_out="$tmp/c-build.txt"
(cd "$tmp/c" && "$leanr" build --no-remote) > "$c_out"
if ! grep -q '^built 0 modules (' "$c_out"; then
    echo "acceptance: FAIL — post-get build ran lean:" >&2
    tail -5 "$c_out" >&2
    exit 1
fi
echo "acceptance: PASS — $(grep '^built ' "$c_out") (prefetch made the build fully local)" >&2

echo "acceptance: PASS — push, remote warm build, A<->B byte-identity, integrity, and cache get all verified" >&2
echo "acceptance: record wall times, module/blob counts, and bytes uploaded in the M2d spec" >&2
