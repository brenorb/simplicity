# Building and checking the jet proofs

This describes how to reproduce the verification of `Coq/C/jet_*.v` from a clean
checkout. What the proofs establish is in [C/JET_PROOFS.md](C/JET_PROOFS.md).

## Current acceptance and trust boundaries

The target is the original production C and canonical Haskell at
`e3b670103101108faa238df012676ff5d8b77cf9`, pinned in
[C/JET_TARGET.md](C/JET_TARGET.md) and `C/jet_source_target.tsv`. The added
`copyWords` helper has been removed; the generated ASTs again use external libc
`memcpy`. Previous acceptance of that helper was about modified C and does not
establish equivalence for the original library.

Current integration counts, conditional scopes and remaining obligations are in
[C/JET_ACCEPTANCE.md](C/JET_ACCEPTANCE.md). Reproduce acceptance on the commit
with `bash Coq/check-jets.sh --accept`; the commit and command are the evidence.
Run output belongs in a temporary directory, not in the repository.

Acceptance checks every module of `_CoqProject.jets`, including the regression
modules, with the kernel and reviewed per-module type/definition and assumption
records. It regenerates all five original ASTs. Source/mutation checks run in
bounded parallel jobs; every command must succeed before proof checking starts.

For an independent batch, use
`bash Coq/check-jets.sh --accept --jets=simplicity_fe_multiply,simplicity_fe_square`.
This checks the selected dependency closure with the same source, kernel and
contract requirements. It does not accept or increase coverage for other jets.

`memcpy_model` remains an explicit premise, with valid source/destination blocks,
readability, destination permissions, positive representable sizes, non-overlap
and address ranges without wraparound. All three model application sites have
compiled proofs of these facts from their existing preconditions. The builtin
copy witness does not prove external libc. Inherited Coq/CompCert assumptions and
physical/logical environment and global-state boundaries remain explicit.

The extended Bitcoin module preserves primitive names/types/tags. Its cached-hash
fields still require a semantic projection from canonical raw transaction/taproot
data. The inherited Bitcoin environment also imposes domain restrictions that
are reported in [C/JET_BITCOIN_MODEL_MISMATCHES.md](C/JET_BITCOIN_MODEL_MISMATCHES.md); the frozen model is unchanged. See [C/JET_FIDELITY_REVIEW.md](C/JET_FIDELITY_REVIEW.md). Treat its
current registered contracts as pending that review.

Final acceptance runs `bash Coq/check-jets.sh --accept` on frozen inputs, without
update/no-build flags. It builds modules, checks the kernel, compares reviewed
axiom and type/definition snapshots, exercises negative fixtures and source/config
pins, and checks all five ASTs. Snapshot generation does not establish acceptance
or canonical fidelity. The broader every-jet proof roadmap remains open.

## Target versus host

The proofs are about generated Clight for **x86-64, little-endian, LP64 with glibc
integer typedefs** (CompCert `x86_64-linux`), compiled with the library's
`PRODUCTION` assertion configuration. That is the *execution target*. It is fixed
by the committed AST (`Coq/C/jets.v`) and by `Archi` in the CompCert build, and
it does not depend on the machine that runs Coq. The host only needs Coq,
OCaml, menhir and a C compiler for CompCert's OCaml tools; the verification was
run on macOS/arm64 and is the same computation on Linux.

Not covered: other ABIs (32-bit, ARM64 native, Windows), fully debug-enabled
assertions (`PRODUCTION` off), and public jets without an inventory proof entry.
Coverage of a family can have width or external-library restrictions stated by
its named theorem; the inventory does not certify whole-evaluator correctness.

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
| CoqPrime | tag `v8.17`, commit `431d7a66877cbe8688fc8864ef892369401440e1`, tarball SHA-256 `cfd5845d…8d90` | only `PocklingtonCertificat.vo` and its standard-integer dependency closure; no bignums/native checker or generator |
| safegcd-bounds | existing pin `06abb7f7aba9b00eb4ead96bdd7dbcc04ec45c4f`, `divsteps_def.v` SHA-256 `f8450b00…aff06` | only the arithmetic definitions and their checked lemmas, not the exhaustive 724-step certificate |

The VST tag records version 2.13 and CompCert 3.13 in its metadata; it builds
against CompCert 3.14 with `IGNORECOMPCERTVERSION=true FLOCQ=bundled`, which the
script sets. Downloads are checksum-verified before use. A stale or partial
download is rejected.

The CoqPrime subset checks the fixed secp256k1 modulus certificate used by
implementation-to-specification bridges. Candidate factors and witnesses are
untrusted data; ordinary checked `vm_compute` verifies their equations and
`coqchk` checks the resulting proof. No new primality assumption, unchecked cast,
or change to the Coq/OCaml baseline is involved. `COQPRIME` may override the
source-tree location, just as `COMPCERT` and `VST` do.
The integrated checker enables `coqchk -bytecode-compiler yes` for checked VM
conversion of these certificates; it still recursively checks every dependency.
For an existing CompCert/VST setup, run `bash Coq/jet-deps.sh --coqprime-only`
to add just this dependency without rebuilding those trees.

The divstep termination proof reuses the existing `C.divstep` arithmetic and
the pinned safegcd definitions. Run `bash Coq/jet-deps.sh --safegcd-only` to
add this small subset to an existing setup. `SAFEGCD` can override its source
directory. The jet Nix build selects the same definitions-only subset with
`cheating = false`; it neither builds nor imports `divsteps724.v` or its
unchecked certificate tactic. The new termination argument uses well-founded
induction, not an assumed or unchecked iteration bound.

## Build and check

```sh
bash Coq/build-jets.sh -j"$(nproc)"     # public proof dependency closure
bash Coq/build-jets.sh --regression -j"$(nproc)"  # optional earlier proofs
bash Coq/check-jets.sh                  # static checks, build, coqchk, assumption gate
bash Coq/jet-sysroot.sh                 # once: pinned glibc headers for the AST check
bash Coq/check-jets.sh --ast            # additionally regenerate and compare the AST
bash Coq/check-jets.sh --accept         # final build, reviewed snapshots and all five ASTs
```

`check-jets.sh` fails when

* the lexical scan finds assumed declarations or unfinished-proof commands in
  jet sources, including inline commands and local/attributed declarations;
  nested comments and strings are excluded. This complements kernel checks;
* a jet module of `_CoqProject.jets` is missing from `_CoqProject`;
* any module that contains a public theorem (`C/jet_public_theorems.txt`) fails
  `coqchk`, or coqchk reports type-in-type, unsafe fixpoints or assumed
  positivity;
* the library-level axiom list printed by `coqchk` differs from
  `C/jet_coqchk_axioms.expected`;
* the axiom set of any public theorem differs from `C/snapshots/*.assumptions`,
  or contains an axiom outside the allowlist in `audit-jet-assumptions.sh`
  (`Print Assumptions` output is an input to this check, not the check);
* a public theorem type or a recorded contract definition differs from
  `C/snapshots/*.contracts`. This catches added impossible premises and changes
  hidden behind predicate aliases, which an assumption-set check cannot detect;
* the isolated negative tests fail to reject an impossible premise, a weakened
  conclusion, a weakened transparent predicate, or proof escape commands;
* with `--ast`, any regenerated core, Bitcoin, SHA, secp256k1 or Elements
  AST differs byte-for-byte from its committed `Coq/C/jets*.v` artifact.

After an intentional change, review the diff and run
`bash Coq/check-jets.sh --update-expected`. Review both the assumption and
contract diffs; this option generates candidate baselines and is never used in
CI. Then rerun `bash Coq/check-jets.sh --accept` with no update flag. Candidate
generation is not evidence of acceptance against reviewed baselines. The fully
explicit type/definition snapshots are conservative:
harmless presentation changes can also require a reviewed update.

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

* `nix-build -A coqJets` builds the public jet dependency closure without the
  secp256k1/modinv verification. Both this derivation and the full `coq`
  derivation run the same static, kernel-safety, library-axiom, per-theorem
  assumption and public-contract checks as the shell workflow. Nix provides
  installed dependencies through Coq's wrapper (`JET_USE_COQPATH=1`); the shell
  path uses the pinned source trees. Their different Flocq packaging is checked
  against the same expected contracts and assumptions.
* The full `coq` derivation remains outside CI because of its measured cost.
  `.github/workflows/ci.yml` has `jets-deps` (cached CompCert/VST), `jets`
  (shell proof build and all gates), `jets-ast` (Linux AST regeneration), and
  `jets-nix` (`coqJets` on Ubuntu with nixos-25.05). Coq is installed by opam in
  each shell proof job. `coqJets` builds only the SHA dependency closure needed
  by these proofs; the full `coq` target retains full VST. The compiled-project
  cache was removed: restored `.vo`
  timestamps could trigger rebuilds, and its earlier claimed benefit was not
  verified.
* The proof target stays `x86_64-linux` on ARM Mac hosts. CompCert's package
  metadata permits that host to build these target semantics.

Both Nix derivations retain C, Haskell and Coq in one filtered source tree and
start the build in its Coq subdirectory. The payload includes the review helper
directories, project variants, snapshots, generation configuration and mismatch
report used by the checks. This keeps the normal repository paths available
without a separate inventory derivation.

Current acceptance and remaining proof obligations are in
[C/JET_ACCEPTANCE.md](C/JET_ACCEPTANCE.md) and
[C/JET_INHERITED_REVIEW.md](C/JET_INHERITED_REVIEW.md).

The removed recursive source-reference gate compared fixed copies of Coq and
Haskell text. It did not construct a proof of their correspondence. The remaining
literal correspondence checks, production-source pins, contract/assumption
snapshots, kernel checks and AST regeneration still run. Removing the fixed
reference loses its additional textual-drift check; it does not establish that
every former comparison is covered elsewhere.
