#!/usr/bin/env bash
# Project-only, pinned interactive backend. Never load the accepted build tree.
set -euo pipefail
project_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
runtime_root="$project_root/.rocq-mcp-local"
if [[ ! -x "$runtime_root/bin/pet" || ! -x "$runtime_root/venv/bin/python" ]]; then
  echo "Project-local rocq-mcp runtime is missing; see proof-work/rocq-mcp/README.md" >&2
  exit 1
fi
# A private copy per server prevents parallel agents from changing each other's
# proof objects or loading stale objects from a different compiler ABI.
if [[ -n "${SIMPLICITY_ROCQ_WORKSPACE:-}" ]]; then
  # The caller may reserve an empty external directory for a reproducible run.
  session_workspace=$(cd -- "$SIMPLICITY_ROCQ_WORKSPACE" && pwd -P)
  case "$session_workspace" in
    "$project_root"|"$project_root"/*)
      echo "Scratch workspace must be outside this repository" >&2; exit 1 ;;
  esac
  if [[ -n "$(ls -A "$session_workspace")" ]]; then
    echo "Requested scratch workspace must be empty" >&2; exit 1
  fi
else
  session_workspace=$(mktemp -d /private/tmp/simplicity-rocq-mcp.XXXXXX)
fi
cp -cR "$runtime_root/workspace-template/." "$session_workspace/"
echo "rocq-mcp scratch workspace: $session_workspace" >&2
export PATH="$runtime_root/bin:$runtime_root/backend/bin:$PATH"
export OPAM_SWITCH_PREFIX="$runtime_root/backend"
export OCAMLPATH="$runtime_root/backend/lib"
export COQLIB="$runtime_root/backend/lib/coq"
export COQCORELIB="$runtime_root/backend/lib/coq-core"
export CAML_LD_LIBRARY_PATH="$runtime_root/backend/lib/stublibs:$runtime_root/backend/lib/ocaml/stublibs"
export ROCQ_COQC_BINARY="$runtime_root/backend/bin/coqc"
export ROCQ_WORKSPACE="$session_workspace"
export ROCQ_DUNE_BUILD=0
export ROCQ_PET_TIMEOUT=20
export ROCQ_QUERY_TIMEOUT_CAP=30
unset OPAMSWITCH OPAM_LAST_ENV
cd -- "$session_workspace"
exec "$runtime_root/venv/bin/python" -c 'from rocq_mcp.server import main; main()'
