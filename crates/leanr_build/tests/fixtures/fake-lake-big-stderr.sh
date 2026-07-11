#!/bin/sh
# Fake `lake translate-config toml <out>` that writes a large amount of
# stderr (bigger than a typical 64KB pipe buffer) and exits nonzero
# quickly, without ever reading/draining anything itself. Regression
# fixture for the stderr-pipe deadlock: if the caller only drains stderr
# after the child exits, this fixture blocks forever on the pipe write
# and the caller has to wait out its whole timeout instead of returning
# promptly with the real diagnostic.
yes "error: ill-formed configuration file, this line pads stderr past a pipe buffer" | head -c 262144 >&2
exit 1
