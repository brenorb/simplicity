#!/usr/bin/env bash
set -euo pipefail

# Coq/startup.  They extend the unaccepted startup sources archived in
# proof-work/sha-support of the main topic checkout; those prerequisites are
# not copied into this branch.  SHA_SUPPORT must point at that directory; the
# two files used are verified against startup/PREREQUISITES.sha256 and
# extracted to startup/prereq (ignored by git) under the logical name
# JetStartupReview that they were written for.
#
# The accepted modules they import must already be built in this tree
# (targets: the SHA-unit jet modules of _CoqProject.jets).
# Usage: SHA_SUPPORT=DIR bash build-startup.sh [--check]
cd "$(dirname "$0")"
: "${SHA_SUPPORT:?Set SHA_SUPPORT to the proof-work/sha-support directory holding the prerequisites}"
mkdir -p startup/prereq
order=(jet_clight_forward jet_sha_initial_globals)
while read -r hash name; do
  actual=$(shasum -a 256 "$SHA_SUPPORT/$name" | awk '{print $1}')
  if [[ "$actual" != "$hash" ]]; then
    echo "prerequisite $name differs from the recorded version" >&2; exit 1
  fi
  cmp -s "$SHA_SUPPORT/$name" "startup/prereq/${name%.source}" || cp "$SHA_SUPPORT/$name" "startup/prereq/${name%.source}"
done < startup/PREREQUISITES.sha256
if grep -nE '\b(admit|Admitted|Axiom|Parameter|Conjecture)\b' startup/proofs/*.v; then
  echo "forbidden declaration in startup sources" >&2; exit 1
fi
paths=(-Q startup/prereq JetStartupReview -Q startup/proofs JetStartup)
ulimit -s 65520 2>/dev/null || true
for name in "${order[@]}"; do
  [[ "startup/prereq/$name.vo" -nt "startup/prereq/$name.v" ]] || bash build-jets.sh --coqc "${paths[@]}" "startup/prereq/$name.v"
done
modules=(jet_sha_startup_globals jet_sha_startup_state jet_sha_startup_jets jet_sha_startup_env_jets jet_sha_startup_setup)
for name in "${modules[@]}"; do
  bash build-jets.sh --coqc "${paths[@]}" "startup/proofs/$name.v"
done
if [[ "${1:-}" == --check ]]; then
  tmp=$(mktemp -d "${TMPDIR:-/tmp}/simplicity-startup-audit.XXXXXX")
  python3 startup/audit-startup.py gen startup/proofs "$tmp/audit.v"
  bash build-jets.sh --coqc "${paths[@]}" -Q "$tmp" StartupAudit "$tmp/audit.v" > "$tmp/audit.log" 2>&1
  python3 startup/audit-startup.py check startup/proofs "$tmp/audit.log"
  bash build-jets.sh --coqchk "${paths[@]}" -silent -o "${modules[@]/#/JetStartup.}" > "$tmp/coqchk.log" 2>&1
  echo "coqchk passed for ${modules[*]} and their dependencies"
  echo "logs: $tmp"
fi
