#!/bin/sh
# Full-stdlib differential gate (Task 6 acceptance): runs `leanr check --all`
# three ways — the sequential reference (`--sequential`, i.e. `replay`), and
# the parallel driver at `--jobs 1` and `--jobs 8` — over every `.olean`
# under the pinned toolchain's lib dir, and asserts the three final
# "checked N modules, M declarations (skipped K unsafe/partial)" stdout
# lines are byte-identical. A mismatch means the parallel driver disagrees
# with the sequential reference on real stdlib content — a real finding,
# not something to paper over.
set -eu

libdir=$(lean --print-libdir)

run() {
    # $1: extra leanr args (word-split intentionally — always simple flags)
    # shellcheck disable=SC2086
    cargo run --release -p leanr_cli -- check --all --path "$libdir" $1 | grep '^checked '
}

echo "check-differential: running --sequential ..." >&2
seq_line=$(run "--sequential")
echo "check-differential: running --jobs 1 ..." >&2
jobs1_line=$(run "--jobs 1")
echo "check-differential: running --jobs 8 ..." >&2
jobs8_line=$(run "--jobs 8")

echo "sequential: $seq_line"
echo "jobs=1:     $jobs1_line"
echo "jobs=8:     $jobs8_line"

if [ "$seq_line" != "$jobs1_line" ] || [ "$seq_line" != "$jobs8_line" ]; then
    echo "check-differential: MISMATCH — parallel driver disagrees with the sequential reference" >&2
    exit 1
fi

echo "check-differential: OK — all three stats lines are byte-identical"
