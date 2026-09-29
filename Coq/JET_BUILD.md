# Building and checking the jet proofs

This describes how to reproduce the verification of `Coq/C/jet_*.v` from a clean
checkout. What the proofs establish is in [C/JET_PROOFS.md](C/JET_PROOFS.md).

## Target versus host

The proofs are about generated Clight for **x86-64, little-endian, LP64 with glibc
integer typedefs** (CompCert `x86_64-linux`), compiled with the library's
`PRODUCTION` assertion configuration. That is the *execution target*. It is fixed
by the committed AST (`Coq/C/jets.v`) and by `Archi` in the CompCert build, and
it does not depend on the machine that runs Coq. The host only needs Coq,
OCaml, menhir and a C compiler for CompCert's OCaml tools; the verification was
run on macOS/arm64 and is the same computation on Linux.

Not covered: other ABIs (32-bit, ARM64 native, Windows), fully debug-enabled
assertions (`PRODUCTION` off), and jets wider than 64 bits.

## Prerequisites

* Coq 8.17.1 on `PATH` (for example an opam switch with OCaml 4.14.1):

  ```sh
  opam switch create simplicity ocaml-base-compiler.4.14.1
  opam install coq.8.17.1 menhir
  eval $(opam env --switch=simplicity)
  ```

* `curl`, `make`, `tar`, `ar`, a C compiler and `clang` (the last only for the AST
  check, used as a C preprocessor, never to compile the jets).

## Pinned dependencies

```sh
bash Coq/jet-deps.sh          # downloads, verifies and builds; ~4 minutes
```

`jet-deps.sh` installs into `JET_DEPS` (default `~/.cache/simplicity-jet-deps`):

| Component | Pin | Notes |
| --- | --- | --- |
| CompCert | 3.14, tarball SHA-256 `5588747d…af20` (the hash pinned in `compcert-opensource.nix`) | configured `x86_64-linux`, with `clightgen` |
| VST | tag `v2.14`, commit `e1db53a4e22ddd3f8223532ba73127b706faf1b3`, tarball SHA-256 `c11551c4…6c06` | only the `sha` library that `Simplicity.Word` imports is built |

The VST tag records version 2.13 and CompCert 3.13 in its metadata; it builds
against CompCert 3.14 with `IGNORECOMPCERTVERSION=true FLOCQ=bundled`, which the
script sets. Downloads are checksum-verified before use. A stale or partial
download is rejected.

## Build and check

```sh
bash Coq/build-jets.sh -j"$(nproc)"     # every module of Coq/_CoqProject.jets
bash Coq/check-jets.sh                  # static checks, build, coqchk, assumption gate
bash Coq/jet-sysroot.sh                 # once: pinned glibc headers for the AST check
bash Coq/check-jets.sh --ast            # additionally regenerate and compare the AST
```

`check-jets.sh` fails when

* a jet source contains `Axiom`, `Parameter`, `Admitted`, `admit` or `Abort`;
* a jet module of `_CoqProject.jets` is missing from `_CoqProject`;
* any module that contains a public theorem (`C/jet_public_theorems.txt`) fails
  `coqchk`, or coqchk reports type-in-type, unsafe fixpoints or assumed
  positivity;
* the library-level axiom list printed by `coqchk` differs from
  `C/jet_coqchk_axioms.expected`;
* the axiom set of any public theorem differs from `C/jet_assumptions.expected`,
  or contains an axiom outside the allowlist in `audit-jet-assumptions.sh`
  (`Print Assumptions` output is an input to this check, not the check);
* with `--ast`, the regenerated AST differs byte-for-byte from `Coq/C/jets.v`.

After an intentional change, review the diff and run
`bash Coq/check-jets.sh --update-expected`.

For a short proof cycle use the prepared load paths (they do not rebuild
dependencies; rebuild imported modules first):

```sh
bash Coq/build-jets.sh --coqc -q C/jet_read16_layout_exec.v   # paths relative to Coq/
bash Coq/build-jets.sh --coqtop -quiet
bash Coq/build-jets.sh --coqchk -silent C.jet_read16_layout_exec
```

Use `--coqc` for final acceptance of a scratch proof: an interactive session can
continue after an error, and a stale `.vo` is not evidence that the current `.v`
compiles.

## Regenerating and checking the AST

`Coq/C/jets.v` is produced by CompCert's `clightgen` from the real sources via
`Coq/C/jet_translation_unit.c`, which includes `C/frame.c` and `C/jets.c`
without replacements. Trust boundary:

* **Checked by Coq:** everything about the Clight program `prog` in `jets.v`.
* **Not checked by Coq:** that `jets.v` faithfully represents the C sources. This
  rests on CompCert's C front end (`clightgen`), Clang used only as a
  preprocessor, and the pinned glibc headers, and is checked only by
  regeneration.
* **Not claimed:** that the C source compiles to correct machine code, or that a
  different compiler or optimisation level preserves these results.

```sh
COMPCERT="$JET_DEPS/compcert-3.14" JET_SYSROOT="$JET_DEPS/sysroot-glibc-2.36" \
  bash Coq/C/check-jets-generation.sh
```

The pinned headers are Debian `libc6-dev_2.36-9+deb12u14_amd64.deb`, SHA-256
`0218fc2befcd784c1b0c6292c0a137ce89fad054efaa579ad083bee0f2c01aae`
(`jet-sysroot.sh` verifies it and extracts only the data archive into `JET_DEPS`).
The check writes only to a fresh temporary directory. Regenerating the committed
artifact (`Coq/C/regenerate-jets.sh` without an output path) is deliberate and
uses `JET_ASSERTIONS=production`; the `debug` and `reckless` modes require an
explicit output path, are rejected otherwise, and are not proof-coverage claims.
Linux target headers are selected explicitly, so host SDK headers cannot leak into
the translation; there are no replacement libc headers and no edited generated
bodies. Never regenerate for a different host ABI or assertion mode without
redoing the proofs against the new AST.

## Nix and CI

* `nix-build -A coqJets` builds `Simplicity.Coq.Jets.nix`: the Simplicity library
  and the jet proofs, with coqchk over the public-theorem modules, and none of the
  secp256k1/modinv verification. The jet modules are also listed in
  `Coq/_CoqProject`, so the full `coq` derivation builds them too.
* The full `coq` derivation stays out of the CI matrix (it exceeds six hours).
  `.github/workflows/ci.yml` instead has three jobs: `jets-deps` builds and caches
  the pinned CompCert/VST (keyed on `Coq/jet-deps.sh`); `jets` restores that cache,
  restores an exact-key cache of the compiled `Simplicity/` modules and of the
  slow serial base `jets`, `jet_exec`, `jet_write8` (never a partial key, since a
  restored `.vo` older than its source would be stale), and runs
  `check-jets.sh`; `jets-ast` regenerates the AST in parallel.

The Nix derivation and the workflow have been syntax-checked but **not executed**
in the environment where this branch was prepared (no Nix installation, no
GitHub runner); the scripts they call were run directly.

## Measured costs

Clean build of all `_CoqProject.jets` modules (2026-09-27, macOS/arm64, 18 cores,
`-j12`): 13 min 38 s wall, 837 s CPU. CompCert 3.14 (`-j16`): 3 min 38 s; the VST
`sha` subset: 9 s. The largest files: `jet_write8.v` 287 s, `jet_exec.v` 229 s,
`check_jet_assumptions.v` 178 s, `jet_read8_two_words.v` 98 s,
`Simplicity/SHA256.v` 89 s, `jet_read8_layout_total.v` 55 s. The two largest
are dominated by closed computations on the generated helper bodies:
`jet_write8.v` by one 216 s `cbn; reflexivity` and two ~35 s `exec_set` steps,
`jet_exec.v` by one 127 s `cbn; reflexivity` and several ~33 s evaluations.
`check_jet_assumptions.v` is 178 s of `Print Assumptions` over intermediate
theorems; `jet_read8_two_words.v` and `jet_read8_layout_total.v` spend ~50 s on
each of a few `eapply` unifications. The build is a serial chain
(`jets` → `jet_exec` → `jet_write8` → readers), so wall time (13 min 38 s) is close to
CPU time (837 s) and `-j` does not shorten it; that chain is what the CI cache
covers.
`coqchk` over the 25 public modules and their dependencies: about 40 s; the
assumption gate: about 60 s.

Timeouts: 18 jet files set `Set Default Timeout 10` and several use
`timeout 10` for speculative reductions. In the baseline the slowest guarded
sentence took 5.3 s (`jet_write_wide_layout.v`); all others took at most 2.3 s.
Only `jet_write_wide_layout.v` was raised, to 30 s. The bounds stay in place
so a runaway reduction still fails quickly.

## Verification record

Independently reproduced, macOS/arm64 host, Coq 8.17.1, OCaml 4.14.1, on a fresh
`git clone` of `feat/jet-equivalence` with an empty `JET_DEPS`, using only the
committed scripts (2026-09-28/29):

* `jet-deps.sh`: CompCert 3.14 (x86_64-linux) and the VST `sha` subset built in
  1 min 48 s (18 cores); both tarballs matched their pinned SHA-256.
* `check-jets.sh`: all `_CoqProject.jets` modules built from scratch (9 min 37 s
  wall for build, coqchk and gate together); `coqchk` passed on the 25 modules
  with public theorems; the assumption gate reported 77 theorems, 10 closed,
  all axiom sets equal to `C/jet_assumptions.expected`; the library-level coqchk
  axioms equal `C/jet_coqchk_axioms.expected`.
* `check-jets.sh --ast` after `jet-sysroot.sh`: the regenerated AST equals the
  committed `Coq/C/jets.v` byte-for-byte (glibc headers matched the pinned
  SHA-256).
* Negative test: editing one recorded assumption set makes the gate fail with a
  diff.

Not executed in this environment: the Nix derivations (`coqJets`, and the full
`coq` derivation with the jet modules added to `_CoqProject`), the GitHub Actions
workflow, and AST regeneration on a Linux host. Earlier claims in the branch
history that the 16/32/64-bit results were re-checked before this rebuild are
historical; the record above supersedes them.
