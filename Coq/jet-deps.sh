#!/usr/bin/env bash
# Fetch, verify and build the pinned dependencies of the jet proofs:
#   * CompCert 3.14 configured for the proved target (x86-64, little-endian,
#     LP64, Linux/glibc; "x86_64-linux") together with its clightgen tool;
#   * the part of VST 2.14 that Simplicity.Word imports (the sha library and
#     the VST modules it needs), built against that CompCert;
#   * the standard-integer Pocklington certificate checker from CoqPrime,
#     without its bignums-based accelerated checker or certificate generator.
#
# The target configuration describes the machine whose C semantics is being
# reasoned about; it is independent of the host that runs Coq.  The host only
# needs a C compiler (used to build CompCert's tools), OCaml, menhir and the
# Coq version below.
#
# Usage: Coq/jet-deps.sh          (uses JET_DEPS, default ~/.cache/simplicity-jet-deps)
#        Coq/jet-deps.sh --coqprime-only   (preserves existing CompCert/VST trees)
# Afterwards the other scripts find the result through JET_DEPS.
set -euo pipefail
coqprime_only=false
case "${1:-}" in
  "") ;;
  --coqprime-only) coqprime_only=true ;;
  *) echo "usage: $0 [--coqprime-only]" >&2; exit 2 ;;
esac
[[ "$#" -le 1 ]] || { echo "usage: $0 [--coqprime-only]" >&2; exit 2; }

COQ_VERSION=8.17.1
COMPCERT_VERSION=3.14
COMPCERT_URL=https://github.com/AbsInt/CompCert/archive/v${COMPCERT_VERSION}.tar.gz
COMPCERT_SHA256=5588747dbc897872aef4795db7c92ba3f9384f5f2ac1bc455e3b01b2d3c9af20
VST_TAG=v2.14
VST_COMMIT=e1db53a4e22ddd3f8223532ba73127b706faf1b3
VST_URL=https://github.com/PrincetonUniversity/VST/archive/${VST_TAG}.tar.gz
VST_SHA256=c11551c454057b8a6c7a958534f3ec783e09450ff7e373bfb7c3d6c009d46c06
# Library files of VST that Simplicity imports (see Simplicity/Word.v and
# Simplicity/Alg.v); make builds their prerequisites.
VST_TARGETS="sha/general_lemmas.vo sha/SHA256.vo sha/functional_prog.vo"
COQPRIME_COMMIT=431d7a66877cbe8688fc8864ef892369401440e1
COQPRIME_URL=https://github.com/thery/coqprime/archive/${COQPRIME_COMMIT}.tar.gz
COQPRIME_SHA256=cfd5845d37987cff2c0f028b3f9f18a80716e255ac6379b41af1ebfffae88d90

JET_DEPS=${JET_DEPS:-${XDG_CACHE_HOME:-$HOME/.cache}/simplicity-jet-deps}
jobs=${JOBS:-$( (nproc || sysctl -n hw.ncpu) 2>/dev/null || echo 2)}

sha256() { if command -v sha256sum >/dev/null; then sha256sum "$1"; else shasum -a 256 "$1"; fi | cut -d' ' -f1; }

have=$(coqc --version 2>/dev/null | sed -n '1s/.*version \([0-9.]*\).*/\1/p')
if [[ "$have" != "$COQ_VERSION" ]]; then
  printf 'Coq %s is required (found %s). See Coq/JET_BUILD.md.\n' "$COQ_VERSION" "${have:-none}" >&2
  exit 1
fi

mkdir -p "$JET_DEPS/src"
fetch() { # url sha256 file
  if [[ ! -f "$JET_DEPS/src/$3" ]]; then curl -fsSL -o "$JET_DEPS/src/$3" "$1"; fi
  if [[ "$(sha256 "$JET_DEPS/src/$3")" != "$2" ]]; then
    printf 'Checksum mismatch for %s\n' "$3" >&2; rm -f "$JET_DEPS/src/$3"; exit 1
  fi
}
if ! $coqprime_only; then
  fetch "$COMPCERT_URL" "$COMPCERT_SHA256" compcert-$COMPCERT_VERSION.tar.gz
  fetch "$VST_URL" "$VST_SHA256" vst-2.14.tar.gz
fi
fetch "$COQPRIME_URL" "$COQPRIME_SHA256" coqprime-8.17.tar.gz

cc_dir=$JET_DEPS/compcert-$COMPCERT_VERSION
if ! $coqprime_only && [[ ! -f "$cc_dir/.built" ]]; then
  rm -rf "$cc_dir"; mkdir -p "$cc_dir"
  tar -xzf "$JET_DEPS/src/compcert-$COMPCERT_VERSION.tar.gz" -C "$cc_dir" --strip-components=1
  ( cd "$cc_dir"
    ./configure -clightgen x86_64-linux
    make depend
    make -j"$jobs" proof
    make -j"$jobs" clightgen
    make -j"$jobs" export/Clightdefs.vo compcert.config
    touch .built )
fi

vst_dir=$JET_DEPS/vst-2.14
if ! $coqprime_only && [[ ! -f "$vst_dir/.built" ]]; then
  rm -rf "$vst_dir"; mkdir -p "$vst_dir"
  tar -xzf "$JET_DEPS/src/vst-2.14.tar.gz" -C "$vst_dir" --strip-components=1
  # The v2.14 tag records version 2.13 and pins CompCert 3.13 in its metadata;
  # it builds against CompCert 3.14 with the version check disabled.
  ( cd "$vst_dir"
    make -j"$jobs" COMPCERT=inst_dir COMPCERT_INST_DIR="$cc_dir" \
      IGNORECOMPCERTVERSION=true FLOCQ=bundled $VST_TARGETS
    touch .built )
fi

prime_dir=$JET_DEPS/coqprime-8.17
if [[ ! -f "$prime_dir/src/Coqprime/PrimalityTest/PocklingtonCertificat.vo" ]]; then
  mkdir -p "$prime_dir"
  tar -xzf "$JET_DEPS/src/coqprime-8.17.tar.gz" -C "$prime_dir" --strip-components=1
  ( cd "$prime_dir"
    make -j"$jobs" src/Coqprime/PrimalityTest/PocklingtonCertificat.vo )
fi

if ! $coqprime_only; then
  cat <<MSG
CompCert $COMPCERT_VERSION (x86_64-linux target): $cc_dir
VST ${VST_TAG} (commit $VST_COMMIT, sha subset):   $vst_dir
MSG
fi
cat <<MSG
CoqPrime v8.17 (commit $COQPRIME_COMMIT, standard-integer checker): $prime_dir
Use with: JET_DEPS=$JET_DEPS bash Coq/build-jets.sh
MSG
