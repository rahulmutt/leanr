#!/bin/sh
# Fake `lake translate-config toml <out>` for bridge unit tests:
# $1=translate-config $2=toml $3=<out>. Emits a minimal valid config and
# records its cwd so the test can assert it ran in the package dir.
printf 'name = "fake"\n\n[[lean_lib]]\nname = "Fake"\n' > "$3"
pwd > "${FAKE_LAKE_CWD_FILE:-/dev/null}"
