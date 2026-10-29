#!/usr/bin/env bash
# Extend the pinned proof dependency with its finite curve-group library.
# Keep the frozen bootstrap, compiler pins and C-generation settings intact.
set -euo pipefail
script_dir=$(cd "$(dirname "$0")" && pwd)
bash "$script_dir/jet-deps.sh" --coqprime-only
jet_dep_root=${JET_DEPS:-${XDG_CACHE_HOME:-$HOME/.cache}/simplicity-jet-deps}
prime_dir=$jet_dep_root/coqprime-8.17
make -C "$prime_dir" -j"${JOBS:-2}" \
  src/Coqprime/elliptic/SMain.vo src/Coqprime/elliptic/GZnZ.vo
