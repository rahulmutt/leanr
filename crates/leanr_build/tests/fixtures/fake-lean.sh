#!/bin/sh
# Fake `lean` for compile-layer unit tests. Understands the argv shape
# compile.rs produces: <src> -o <olean> -i <ilean> --setup <setup> --json.
# FAKE_LEAN_FAIL_ON=<substr>: for a matching <src>, write a partial
# olean, emit one JSON diagnostic on stdout, exit 1.
src=""; o=""; i=""; setup=""
while [ $# -gt 0 ]; do
  case "$1" in
    -o) o="$2"; shift 2 ;;
    -i) i="$2"; shift 2 ;;
    --setup) setup="$2"; shift 2 ;;
    --json) shift ;;
    +*) shift ;;
    -*) shift ;;
    *) src="$1"; shift ;;
  esac
done
[ -f "$setup" ] || { echo "fake-lean: missing setup file $setup" >&2; exit 3; }
mkdir -p "$(dirname "$o")" "$(dirname "$i")"
case "$src" in
  *"${FAKE_LEAN_FAIL_ON:-@@never@@}"*)
    printf 'partial' > "$o"
    printf '{"severity":"error","pos":{"line":3,"column":7},"fileName":"%s","data":"unknown identifier `nope`"}\n' "$src"
    exit 1 ;;
esac
printf 'olean:%s' "$src" > "$o"
printf 'ilean:%s' "$src" > "$i"
exit 0
