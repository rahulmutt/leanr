#!/bin/sh
# Fake `lake translate-config toml <out>` that mimics real lake's refusal
# to overwrite an existing out-file (bridge.rs's
# `concurrent_load_config_calls_on_the_same_lakefile_never_collide_on_tmp_path`
# regression test): $1=translate-config $2=toml $3=<out>.
if [ -e "$3" ]; then
  echo "error: output configuration file already exists: $3" >&2
  exit 1
fi
printf 'name = "fake"\n\n[[lean_lib]]\nname = "Fake"\n' > "$3"
