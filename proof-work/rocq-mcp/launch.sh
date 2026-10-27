#!/bin/bash
# Start the tested backend without touching the live checkout's proof objects.
set -euo pipefail

project_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
runtime_dir="$project_dir/.rocq-mcp-local"
template_dir="$runtime_dir/workspace-template"

for required in "$runtime_dir/venv/bin/python" "$runtime_dir/bin/pet" "$runtime_dir/backend/bin/coqc"; do
  if [[ ! -x "$required" ]]; then
    echo "rocq-mcp: missing runtime executable: $required" >&2
    exit 1
  fi
done
if [[ ! -f "$template_dir/_CoqProject" ]]; then
  echo "rocq-mcp: missing compatible workspace template: $template_dir" >&2
  exit 1
fi

if [[ -n "${SIMPLICITY_ROCQ_WORKSPACE:-}" ]]; then
  if [[ ! -d "$SIMPLICITY_ROCQ_WORKSPACE" ]]; then
    echo "rocq-mcp: SIMPLICITY_ROCQ_WORKSPACE must name an existing empty directory" >&2
    exit 1
  fi
  workspace_dir="$(cd "$SIMPLICITY_ROCQ_WORKSPACE" && pwd -P)"
  case "$workspace_dir/" in
    "$project_dir/"*)
      echo "rocq-mcp: the workspace must be outside the live checkout" >&2
      exit 1
      ;;
  esac
  if [[ -n "$(ls -A "$workspace_dir")" ]]; then
    echo "rocq-mcp: refusing a nonempty workspace: $workspace_dir" >&2
    exit 1
  fi
else
  workspace_dir="$(mktemp -d /private/tmp/simplicity-rocq-mcp.XXXXXX)"
fi

# APFS clones keep each server's mutable files separate without a full copy.
# If cloning is unavailable, fail rather than silently share mutable objects.
/bin/cp -cR "$template_dir/." "$workspace_dir/"

export PATH="$runtime_dir/bin:$runtime_dir/backend/bin:$PATH"
export OPAM_SWITCH_PREFIX="$runtime_dir/backend"
export OCAMLLIB="$runtime_dir/backend/lib/ocaml"
export OCAMLPATH="$runtime_dir/backend/lib"
export CAML_LD_LIBRARY_PATH="$runtime_dir/backend/lib/stublibs"
export COQLIB="$runtime_dir/backend/lib/coq"
export COQCORELIB="$runtime_dir/backend/lib/coq-core"
unset COQPATH
export ROCQ_COQC_BINARY="$runtime_dir/backend/bin/coqc"
export ROCQ_WORKSPACE="$workspace_dir"
export PYTHONDONTWRITEBYTECODE=1

echo "rocq-mcp: isolated workspace: $workspace_dir" >&2
echo "rocq-mcp: seed is a historical snapshot, not the live checkout; rebuild copied current sources before debugging new proofs" >&2
cd "$workspace_dir"
exec "$runtime_dir/venv/bin/python" -c 'from rocq_mcp.server import main; main()'
