#!/usr/bin/env bash
set -euo pipefail

# Build the Elements environment-unit derived tree, check that the generated
# ports are current, reject admissions, audit the assumptions of the result
# theorem and kernel-check it with its whole dependency chain.
cd "$(dirname "$0")"
root=$PWD
tmp=$(mktemp -d "${TMPDIR:-/tmp}/simplicity-elements-env.XXXXXX")
mkdir "$tmp/C"
python3 elements-env/gen-elements-env-ports.py "$tmp/C" > /dev/null
for f in "$tmp"/C/*.v; do
  cmp "$f" "elements-env/C/$(basename "$f")" || { echo "stale generated module $(basename "$f")" >&2; exit 1; }
done
if grep -nE '\b(admit|Admitted|Axiom|Parameter|Conjecture)\b' elements-env/C/*.v; then
  echo "forbidden declaration in elements-env sources" >&2; exit 1
fi
bash build-elements-env.sh ${JOBS:--j4}
{
  echo "Require C.jet_elements_env_tapenv C.jet_elements_env_tomidstate C.jet_elements_env_ctxo."
  echo "Require C.jet_elements_env_tapenv_relations C.jet_elements_tappath_nullable."
  echo "Require C.jet_elements_env_free C.jet_elements_env_txenv."
  echo "Require C.jet_elements_env_txenv_relations C.jet_elements_env_hashbuffer C.jet_elements_env_bytestring."
  echo "Require C.jet_elements_env_readbe64 C.jet_elements_env_copyrawamt."
  for r in jet_elements_env_tomidstate.eval_sha256_toMidstate jet_elements_env_ctxo.ctxo_hash jet_elements_env_tapenv.eval_mallocTapEnv \
      jet_elements_tappath_nullable.elements_tappath_nullable_local_spec \
      jet_elements_env_tapenv_relations.el_ready_script_cmr jet_elements_env_tapenv_relations.el_ready_internal_key \
      jet_elements_env_tapenv_relations.el_ready_tapleaf_version jet_elements_env_tapenv_relations.el_ready_tappath \
      jet_elements_env_free.eval_freeTransaction jet_elements_env_free.eval_freeTapEnv \
      jet_elements_env_txenv.eval_build_txEnv \
      jet_elements_env_txenv_relations.el_ready_genesis_block_hash jet_elements_env_txenv_relations.el_ready_current_index \
      jet_elements_env_hashbuffer.eval_hashBuffer jet_elements_env_bytestring.hash_buffer_bytestring \
      jet_elements_env_readbe64.eval_sha_ReadBE64 jet_elements_env_readbe64.c_be64_value \
      jet_elements_env_copyrawamt.eval_copyRawAmt_null jet_elements_env_copyrawamt.eval_copyRawAmt_explicit \
      jet_elements_env_copyrawamt.eval_copyRawAmt_confidential; do
    printf 'Goal True. idtac "@@ %s". Abort.\nPrint Assumptions C.%s.\n' "${r#*.}" "$r"
  done
} > "$tmp/audit.v"
cd "$root/elements-env/tree"
ulimit -s 65520 2>/dev/null || true
bash build-jets.sh --coqc -Q "$tmp" ElementsEnvAudit "$tmp/audit.v" > "$tmp/audit.log" 2>&1
python3 "$root/elements-sha/audit.py" "$tmp/audit.log" 20
bash build-jets.sh --coqchk -silent -o C.jet_elements_env_tapenv C.jet_elements_env_tapenv_relations C.jet_elements_env_free C.jet_elements_env_txenv_relations C.jet_elements_env_bytestring C.jet_elements_env_copyrawamt > "$tmp/coqchk.log" 2>&1
echo "coqchk passed for C.jet_elements_env_tapenv, C.jet_elements_env_tapenv_relations (with C.jet_elements_tappath_nullable), C.jet_elements_env_free, C.jet_elements_env_txenv_relations (with C.jet_elements_env_txenv), C.jet_elements_env_bytestring (with C.jet_elements_env_hashbuffer), C.jet_elements_env_copyrawamt (with C.jet_elements_env_readbe64) and their dependencies"
echo "logs: $tmp"
