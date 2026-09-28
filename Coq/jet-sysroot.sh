#!/usr/bin/env bash
# Fetch the pinned amd64 glibc headers used to regenerate the jet AST.
# Only the Debian package's data archive is extracted, into JET_DEPS; nothing is
# installed on the host.  Prints the value for JET_SYSROOT.
set -euo pipefail
DEB=libc6-dev_2.36-9+deb12u14_amd64.deb
URL=https://deb.debian.org/debian/pool/main/g/glibc/$DEB
SHA256=0218fc2befcd784c1b0c6292c0a137ce89fad054efaa579ad083bee0f2c01aae
JET_DEPS=${JET_DEPS:-${XDG_CACHE_HOME:-$HOME/.cache}/simplicity-jet-deps}
sha256() { if command -v sha256sum >/dev/null; then sha256sum "$1"; else shasum -a 256 "$1"; fi | cut -d' ' -f1; }
mkdir -p "$JET_DEPS/src"
if [[ ! -f "$JET_DEPS/src/$DEB" ]]; then curl -fsSL -o "$JET_DEPS/src/$DEB" "$URL"; fi
[[ "$(sha256 "$JET_DEPS/src/$DEB")" == "$SHA256" ]] || { echo "checksum mismatch for $DEB" >&2; rm -f "$JET_DEPS/src/$DEB"; exit 1; }
root=$JET_DEPS/sysroot-glibc-2.36
if [[ ! -f "$root/.extracted" ]]; then
  rm -rf "$root"; mkdir -p "$root"
  tmp=$(mktemp -d); ( cd "$tmp" && ar x "$JET_DEPS/src/$DEB" && ls )
  data=$(ls "$tmp"/data.tar.* | head -1)
  tar -xf "$data" -C "$root"; rm -rf "$tmp"; touch "$root/.extracted"
fi
echo "JET_SYSROOT=$root"
