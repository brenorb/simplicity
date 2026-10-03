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
bash Coq/build-jets.sh -j"$(nproc)"     # public proof dependency closure
bash Coq/build-jets.sh --regression -j"$(nproc)"  # optional earlier proofs
bash Coq/check-jets.sh                  # static checks, build, coqchk, assumption gate
bash Coq/jet-sysroot.sh                 # once: pinned glibc headers for the AST check
bash Coq/check-jets.sh --ast            # additionally regenerate and compare the AST
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
* the axiom set of any public theorem differs from `C/jet_assumptions.expected`,
  or contains an axiom outside the allowlist in `audit-jet-assumptions.sh`
  (`Print Assumptions` output is an input to this check, not the check);
* a public theorem type or a recorded contract definition differs from
  `C/jet_contracts.expected`. This catches added impossible premises and changes
  hidden behind predicate aliases, which an assumption-set check cannot detect;
* the isolated negative tests fail to reject the review's impossible-premise
  attack or the previously missed inline/local/attributed proof escapes;
* with `--ast`, the regenerated AST differs byte-for-byte from `Coq/C/jets.v`.

After an intentional change, review the diff and run
`bash Coq/check-jets.sh --update-expected`. Review both the assumption and
contract diffs; this option deliberately accepts changed contracts and is never
used in CI. The fully explicit type/definition snapshots are conservative:
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

Executed checks and remaining host/runner coverage are recorded below. A
configured job does not establish that it has run successfully.

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
(`jets` → `jet_exec` → `jet_write8` → readers), so wall time (13 min 38 s) was close to
CPU time (837 s). These are historical measurements; the current build excludes
the informational assumption dump and reduces the writer computation costs.
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

Not executed in the 2026-09-28/29 reproduction: the Nix derivations (`coqJets`, and the full
`coq` derivation with the jet modules added to `_CoqProject`), the GitHub Actions
workflow, and AST regeneration on a Linux host. Earlier claims in the branch
history that the 16/32/64-bit results were re-checked before this rebuild are
historical; the record above supersedes them.


### Review remediation verification (2026-09-30)

The implementation changes following `JET_EQUIVALENCE_REVIEW.md` were checked
on the same macOS/arm64 host with Coq 8.17.1:

* `check-jets.sh --ast` passed without updating expected results: 144 default
  modules, `coqchk` on 25 public modules with all kernel-safety checks, 89
  public results (10 closed), unchanged inherited assumption sets, matching
  explicit contract snapshots, and byte-identical Clight regeneration.
* `nix-build -A coqJets` completed a clean proof build and the same gates,
  including the negative tests. Proof build: 4 min 54 s; check phase: 2 min 3 s.
  The Nix package uses external Flocq and installed dependencies; the shell
  uses bundled Flocq and source trees. Both passed the same expected records.
* `build-jets.sh --regression -j8` rebuilt and passed the 19 optional earlier
  proof modules and the informational assumption dump. It uses a separate
  generated Makefile so switching project manifests cannot reuse stale
  dependency rules.
* The permanent negative test adds `(1 = 2)%nat` to `add64_guarantees` in an
  isolated built copy: the assumption gate passes, while the contract gate
  rejects the altered statement. Inline `Admitted`, local/attributed `Axiom`,
  `admit` and `Abort` are rejected; nested comments and quoted strings are
  ignored. Both Nix and shell gates run these tests.
* Shell syntax, project-manifest partition, Python syntax, `git diff --check`
  and `codespell` passed. Spelling exemptions are CompCert's `mone` and three
  existing hypothesis identifiers, rather than edits to generated code.
* The full `coq` Nix derivation evaluated successfully; its proof build was not
  run. GitHub Actions and Linux-host AST regeneration remain unexecuted.

The twelve complete calls, canonical/context results and execution guarantees
now quantify over arbitrary environment values. Local guarantees retain the
output, written prefix, final cursor and preservation of loads from initially
valid blocks; each jet also exports a contextual guarantee. The concrete layout
witness additionally proves the ordered gap-buffer predicate in the same memory.

Maintenance changes share the total 16/32/64-bit reader memory proof, the
canonical increment program and integer-interpretation injectivity, and reuse
the existing wide-reader symbol facts. Operator values are explicit in the
writer derivations to avoid normalizing symbolic payloads: the measured
`jet_exec.v` proof compilation fell from about 235 s to 98 s. The broader
width-specific add/increment execution adapters, directory reorganization and
unifying the separate secp256k1 AST pipeline remain possible follow-ups. Debug
assertion coverage and evaluator linking/whole-evaluator correctness remain
explicit scope boundaries, not claims made by these results.

### Constant-jet extension (2026-10-01)

The ten low/high jets at 1/8/16/32/64 bits now have complete generated-Clight
call proofs, canonical local specs, represented-context substitution and
call-boundary guarantees in `C/jet_constant*.v`. They reuse the existing total
writers and derive the entire frame lifecycle from initial permissions, with
arbitrary output contents and non-wrapping cursors, including crossings.

`jet-coverage.py` inventories all three public C jet headers and both
registration catalogs. The current map is 22/533, not every-jet completion;
`--require-complete` fails while any jet lacks an entry. The inventory validates
links to audited direct canonical theorem statements, but the regular kernel,
assumption, contract and AST gates remain the proof evidence. See
[C/JET_ROADMAP.md](C/JET_ROADMAP.md) for the full scope and continuation plan.

The Nix proof sources include the coverage metadata and receive the separately
filtered C header/registration source through `JET_C_REPO`. Negative contract
tests rebuild consumers after mutating a theorem dependency. The contract
snapshot extension adds new entries only; all previous types and inherited
axiom sets remain unchanged.

Local verification on 2026-10-01: `check-jets.sh --ast` passed, including
`coqchk` on 27 public modules, the 105-result assumption audit (11 closed),
the frozen contract comparison, both sets of negative tests and exact AST
regeneration. `build-jets.sh --regression -j12` also passed. These checks
certify the covered jets, not completion of the every-jet goal.
The clean `nix-build -A coqJets` also passed: 3 min 47 s in the proof build,
7 min 23 s in the check phase, including the isolated negative-test rebuild.
The full `coq` derivation was evaluated but not built in this extension.

### Complement-jet extension (2026-10-01)

All five complement jets at 1/8/16/32/64 bits now have complete generated-Clight
call proofs, canonical local specs, represented-context substitution and
deterministic call-boundary guarantees. `C/jet_complement_spec.v` mirrors the
canonical Haskell recursion and proves symbolic bitwise bridges for both
CompCert integer carriers. Byte promotions/casts and the three wide bodies
have separate small execution adapters. `C/jet_readBit_layout.v` supplies the
actual arbitrary-layout bit-reader proof for the one-bit variant and later
single-bit/carry-input jets. No fixed input enumeration or new axioms are used.

The proof map is now 27/533, with 506 jets still uncovered. New public contracts
and assumption snapshots add entries only: prior theorem types and axiom sets
are unchanged. A long qualified theorem name exposed a wrapping bug in the
assumption audit's `Locate` parsing. Explicit theorem-name markers now delimit
the audit, and missing results are checked even when updating expectations;
the inherited axiom allowlist has not changed.

Local `check-jets.sh --update-expected --ast` passed for the complete family,
including `coqchk` on 32 public modules, 128 audited results (15 closed),
contract snapshot generation, negative tests and exact Clight regeneration.
The new snapshots were reviewed: no previous type or assumption entry changed.
The normal comparison gates are also run by the clean Nix proof derivation.
The clean `nix-build -A coqJets --no-out-link` passed for this 27-jet state:
3 min 42 s in the proof build and 7 min 44 s in the check phase, including
the isolated negative-test rebuild. This does not certify later extensions.

### Binary-jet extension (2026-10-01)

All fifteen and/or/xor jets at 1/8/16/32/64 bits now have complete
generated-Clight call proofs against the canonical `Programs.Word.bitwise_bin`
programs, with canonical local specs, represented-context substitution and
deterministic call-boundary guarantees. Shared symbolic bridges handle both
integer carriers. The generated-body adapters handle byte promotions and
truncation, the wide operations, and the one-bit and/or conditional branches.
Both operands are read before writing, even for one-bit and/or. The input-bit
preservation lemma is now shared by single-bit and bit-list contracts.

The proof map is 42/533, with 491 declarations still uncovered.
`check-jets.sh --update-expected --ast` passed, including `coqchk` on 36 public
modules, 161 audited results (18 closed), contract snapshot generation,
negative tests and exact AST regeneration. Snapshot review found additions
only; prior theorem types, assumptions and the inherited allowlist are
unchanged. `build-jets.sh --regression -j12` also passed after rebuilding
consumers of the shared input-layout lemma.

The clean `nix-build -A coqJets --no-out-link` passed for the 42-jet state:
4 min 49 s in the proof build and 8 min 37 s in the check phase, including
normal frozen-contract comparisons and the isolated negative-test rebuild.
The result is `/nix/store/946kw1dy40drsl9qyg4dwcrgdlpnkf8k-Simplicity-coq-jets-0.0.0`.
This does not certify later extensions.

### Wide ternary-jet extension (2026-10-01)

The nine maj/xor_xor/ch jets at 16/32/64 bits now have complete generated-Clight
call proofs, canonical local specs, represented-context substitution and
deterministic call-boundary guarantees. They reuse the existing
`Word.bitwiseTri` program and `bitwiseTri_correct` theorem, checked against
the canonical Haskell recursion and bit operators. Shared symbolic bridges
handle both integer carriers; no larger-word enumeration is used. The actual
ch expression's multiply-by-one, three reader calls, writer call and entire
allocation/copy/free lifecycle are formally discharged. The canonical
three-word input encoding is now a reusable lemma.

The proof map is 51/533, with 482 declarations still uncovered.
`check-jets.sh --update-expected --ast` passed, including `coqchk` on 38 public
modules, 179 audited results (21 closed), negative tests and exact AST
regeneration. Snapshot review found 18 new assumption entries and 469 new
contract lines, with no prior entry changed and no allowlist expansion.
`build-jets.sh --regression -j12` also passed. The clean Nix run started for
the earlier 42-jet state does not certify this ternary extension.

### Complete ternary family (2026-10-01)

The three byte and three one-bit maj/xor_xor/ch calls complete all fifteen
ternary jets at 1/8/16/32/64 bits. The byte adapter handles the actual mixed
promotion semantics (notably ch), then the writer's byte cast. The bit adapter
executes the actual nested maj conditionals, ch branch and xor_xor expression.
All three reads, the write and frame cleanup are derived from initial layout
conditions, with arbitrary output bits and non-wrapping cursors.

Both integrated extension checks passed with exact AST regeneration and
negative tests: the byte extension reached 54/533, 39 public modules and
187 audited results; the bit extension reached 57/533, 40 public modules and
195 audited results. The closed-result count remains 21. Snapshot review
found additions only (byte: 8 assumption entries and 249 contract lines;
bit: 8 assumption entries and 232 contract lines), with all previous contracts,
assumption sets and the inherited allowlist unchanged. There are 476 public
jet declarations still without equivalence proofs.

The clean `nix-build -A coqJets --no-out-link` also passed for the 57-jet
state: 4 min 55 s in the proof build and 9 min 14 s in the check phase,
including normal assumption/contract comparisons and the isolated negative
tests. The result is
`/nix/store/jrpkf1pbqvnc7f2ms4ys7dcjjlcmf1f3-Simplicity-coq-jets-0.0.0`.
Normal local assumption/contract comparisons passed at 195 results (21
closed), and the regression target passed. This Nix result does not certify
the later predicate extension.

### Some/all predicate family (2026-10-01)

All nine publicly declared some/all jets now have complete generated-Clight
call proofs against their canonical recursive Simplicity programs: some at
1/8/16/32/64 bits and all at 8/16/32/64 bits. `predicate_spec_numeric` proves
the shared symbolic bridge by induction; it does not replace the public jet
equivalence proofs. The implementation adapters derive the exact reader value,
actual comparison and cast, one-bit output, frame lifecycle and memory
preservation. They export canonical local specs, represented-context
substitution and deterministic call-boundary guarantees.

The integrated wide extension passed at 63/533, with 43 public modules and
209 audited results (24 closed). The byte/identity extension passed at 66/533,
with 46 public modules and 222 audited results (25 closed). Both checks
included negative tests and exact AST regeneration. Reviewed snapshots add
entries only: wide added 14 assumption entries and 261 contract lines;
byte/identity added 13 assumption entries and 295 contract lines. Previous
contracts and assumption sets are unchanged, with no new axioms or inherited
allowlist expansion. The regression target also passed. There are 467 public
jet declarations without equivalence proofs; the completeness check still
fails as intended. The clean Nix result for 57 jets does not certify this
predicate extension.

### Wide equality (2026-10-01)

The eq_16/32/64 calls now have complete implementation-to-specification proofs
against `Programs.Generic.eq`, mirrored literally in `jet_equality_spec.v`.
The bridge handles the actual sum swap/case routing and product conditional,
then uses exact reader integers rather than lossy decoding. Initial contracts
derive both reads, comparison, bit write, source-frame lifecycle and framing.

The integrated check with `--update-expected --ast` passed at 69/533 with
49 public modules. Snapshot review found additions only: 12 audited results
(four closed) and 222 contract lines, with all previous contracts, assumption
sets and the inherited allowlist unchanged. Negative tests and exact AST
regeneration passed. The latest snapshots contain 234 audited results (29
closed). There are 464 declarations without proof entries; the overall goal
remains incomplete. Earlier Nix results do not certify this extension.

### Byte and bit equality (2026-10-01)

eq_8 and eq_1 extend the same canonical Generic.eq proof family. Both derive
two real reader calls before the bit write and free their local source copy.
The byte expression handles promoted uchar operands and Boolean conversion;
the one-bit expression handles normalized Boolean reader results and casts.
They retain arbitrary unrelated bits, valid non-wrapping cursors and crossings.

The integrated check passed at 71/533 with 52 public modules, including
negative tests and exact AST regeneration. Reviewed snapshots add 11 audited
results (one closed) and 283 contract lines only. Previous theorem types and
assumption sets, and the inherited axiom allowlist, are unchanged. There are
245 audited results (30 closed), and 462 declarations without proof entries.

The earlier clean Nix run also finished successfully at 66/533: the proof
build took 4 min 58 s and checks took 9 min 37 s. Its result is
`/nix/store/9wyvl6bmcqbbpwqr0vl7apqgznw50bvp-Simplicity-coq-jets-0.0.0`.
It certifies the predicate extension, not these later equality additions.

### Carry-input byte increment (2026-10-01)

`full_increment_8` has a complete C-call proof against the existing canonical
`full_increment_word_spec` composition, for both input carry bits. The new
numeric bridge is generic in width; the byte bridge reuses existing adder
representation, overflow and modulo lemmas. The execution proof retains the
actual C promotions, multiply-by-one, Boolean and byte casts. The layout proof
derives the real bit and byte reads, both writes and allocation/copy/free from
initial-only non-wrapping contracts, including crossings and unrelated bits.

The integrated check with exact AST regeneration passed at 72/533 with
54 public modules. Reviewed snapshots add seven audited results (two closed)
and 241 contract lines only, without changing previous contracts, assumption
sets or the inherited axiom allowlist. Negative tests passed. Normal audit
comparisons passed at 252 results (32 closed), and the regression target passed.
There are 461 declarations without proof entries; the completeness check still
fails as intended. A fresh Nix build for this 72-jet state passed; its
derivation is `/nix/store/s5c4wp8gy6ridzgcram2zcfmdrxz51zv-Simplicity-coq-jets-0.0.0.drv`
and source is `/nix/store/g0px66r68291v1cgsxyxrn6q51ws82gd-source`. This is
result is `/nix/store/1yc61chh7mk6q7l4f9l48d66ygxf17hn-Simplicity-coq-jets-0.0.0`.
The proof build took 5 min 28 s and checks took 14 min 47 s. It certifies this
72-jet snapshot, not subsequent extensions.

### Carry-input wide increments (2026-10-01)

`full_increment_16/32/64` reuse the existing increment bridges for carry one
and a shared canonical carry-zero identity. Their actual complete calls retain
the mixed uint/ulong arithmetic, 64-bit wraparound and both output writes.
All helper calls and local cleanup follow from initial-only frame contracts.

The integrated check with exact AST regeneration passed at 75/533 and 56 public
modules, including negative tests. Reviewed snapshots add ten audited results
(two closed) and 303 contract lines only; previous contracts and assumption
sets, and the inherited axiom allowlist, are unchanged. There are 262 audited
results (34 closed) and 458 declarations without proof entries. This extension
is not certified by the earlier clean Nix runs.

### Carry-input byte addition (2026-10-01)

`full_add_8` now has a complete C-call proof against canonical `Word.fullAdder`.
Its symbolic bridge retains the short-circuit carry and byte truncation;
execution includes the actual conditional, three reads and both writes.
Initial-only contracts cover 17 input bits and nine output bits at arbitrary
valid cursors, including crossings and unrelated bits.

The integrated check with exact AST regeneration passed at 76/533 and 58 public
modules, including negative tests. Reviewed snapshots add seven audited results
(two closed) and 260 contract lines only; previous contracts, assumption sets
and the inherited axiom allowlist are unchanged. There are 269 audited results
(36 closed), and 457 declarations without proof entries. The completeness gate
still fails as intended. The 72-jet clean Nix result does not certify this extension.

### Carry-input wide addition (2026-10-01)

`full_add_16/32/64` now share a complete C-call proof against canonical
`Word.fullAdder`. The symbolic bridge reuses the existing add overflow lemmas
and increment threshold while retaining the wrapping 64-bit intermediate sum.
The execution adapters preserve the generated short-circuit carry branch and
the mixed uint/ulong subtraction. All readers, both writers and local cleanup
are derived from initial-only contracts for `1 + 2 * width` input bits and
`1 + width` output bits, with arbitrary valid cursors and memory framing.

The integrated check with exact AST regeneration passed at 79/533 and 60 public
modules, including negative tests. Reviewed snapshots add ten audited results
(two closed) and 279 contract lines only; previous contracts, assumption sets
and the inherited axiom allowlist are unchanged. Normal comparison gates passed
at 279 results (38 closed), and the regression target passed. There are 454
declarations without proof entries; the completeness gate still fails as
intended. The earlier 72-jet clean Nix result does not certify this extension.

A clean Nix rebuild of the committed 79-jet proof snapshot finished with exit 0. Its
derivation is `/nix/store/0ddf7idmj3z95bvswfy9a4af3k5b31g0-Simplicity-coq-jets-0.0.0.drv`
and immutable source is `/nix/store/3fjhp6mq6q85yzjhrswzakv0m75rflz2-source`.
The result is `/nix/store/h7fsjq2bjgjpdz85k5d7y4pyz2kj1pmm-Simplicity-coq-jets-0.0.0`.
Build took 4m52s and check took 9m27s, including kernel checks on 60 public
modules, 279 audited results (38 closed), contract comparison, negative tests
and exact AST regeneration. This certifies the immutable 79-jet snapshot only;
later subtraction work requires its own checks.

## Complete subtraction calls at 8/16/32/64 bits

The four `subtract` calls now target the literal canonical
`Programs.Arith.subtract`/`full_subtract` compositions. The shared bridge
uses the checked full-adder and complement results, a signed borrow/payload
balance and carrier-to-word modulus reduction. Execution retains the byte's
signed promoted comparison, the wide unsigned comparison, multiply-by-one,
casts, both output writes and cleanup. The public contracts assume only the
initial readable inputs and writable output frame, including arbitrary valid
cursors, word crossings and unrelated output bits.

The integrated check with exact AST regeneration finished with exit 0 at
83/533 and 64 public modules. Reviewed snapshots add 25 audited results
(12 closed) and 589 contract lines only; previous contracts, assumption sets
and the inherited axiom allowlist are unchanged. Normal comparison gates passed
at 304 results (50 closed), and the regression target passed. The completeness
gate intentionally fails with 450 missing declarations. The 79-jet clean Nix
result does not certify this extension.

## Shared negate/decrement calls at 8/16/32/64 bits

All eight calls now reuse the canonical subtraction compositions and signed
borrow/payload balance. One symbolic representation module handles both
operations and both machine carriers; the byte/wide execution and memory
modules each share their proof across negate and decrement. They preserve
actual nonzero/less-than-one comparisons, multiply-by-one, unsigned negation,
byte promotions and truncation, modular underflow, both writes and cleanup.
Public contracts require only initial readable inputs and writable output
frames at arbitrary valid cursors, with crossings and unrelated output bits.

The integrated check with exact AST regeneration finished with exit 0 at
91/533 and 67 public modules, including negative tests. Reviewed snapshots
add 23 audited results (five closed) and 499 contract lines only; previous
contracts, assumption sets and the inherited axiom allowlist are unchanged.
There are 327 audited results (55 closed). The regression target passed; the
completeness gate intentionally fails with 442 missing declarations. The
79-jet clean Nix result does not certify these later proof extensions.

Normal assumption and contract comparison gates also finished with exit 0 at
327 results (55 closed), without rewriting the expected snapshots.

A clean Nix rebuild of the committed 91-jet snapshot finished with exit 0. Its
derivation is `/nix/store/kwj8jpi7jdl6vnjra63ym4ary6pdg4mf-Simplicity-coq-jets-0.0.0.drv`
and immutable source is `/nix/store/11vh5glsfycx6nnkxhrji362pnlvm2hs-source`.
The result is `/nix/store/iy1xh1fi775w9pdzh92bs56gq423457p-Simplicity-coq-jets-0.0.0`.
The build phase took 5m18s and the check phase 12m31s. All integrated gates
passed at 67 public modules and 327 audited results (55 closed). This certifies
the immutable 91-jet snapshot, not the subsequent full-decrement extension.

## Borrow-input decrement at all arithmetic widths

`full_decrement_8/16/32/64` now have checked complete C-call proofs against
`full_decrement_word_spec`, with both input borrow values. The shared numeric
bridge reuses `full_subtract_word_spec_numeric` at zero subtrahend and the
checked subtraction carrier-modulo lemmas. Byte and width-shared execution
adapters retain the unsigned multiply-by-one comparison and mixed uint/ulong
promotion. The layout proofs derive every intermediate read, write and local
cleanup from initial-only contracts, including arbitrary valid cursors,
crossings and unrelated output bits.

The integrated check with exact AST regeneration finished with exit 0 at
95/533 and 70 public modules. The reviewed snapshots add 20 audited results
(seven closed) and 447 contract lines only; existing contracts, axiom sets and
the inherited library-level axiom list are unchanged. There are 347 audited
results (62 closed), and 438 declarations still lack complete proofs. The
regression target also finished with exit 0. Normal assumption and contract
comparison gates also passed at 347 results (62 closed), without rewriting
snapshots. The completed clean Nix run certifies a separate 91-jet snapshot.

## Borrow-input subtraction at all arithmetic widths

`full_subtract_8/16/32/64` now have complete C-call proofs against the literal
canonical `full_subtract_word_spec` composition, for both input borrow bits.
The shared representation bridge includes the endpoint `delta = -word_modulus n`.
Both carrier subtractions are handled modularly, and the false first comparison
establishes a non-wrapping intermediate for the second borrow comparison.
The execution adapters follow the actual conditional assigning `_t'4` and
retain unsigned byte comparisons and mixed uint/ulong wide comparisons.
The initial-only layout contracts derive all three reads, both writers and
cleanup, with arbitrary valid cursors, crossings and memory framing.

The integrated check with exact AST regeneration finished with exit 0 at
99/533 and 73 public modules, including negative tests. Reviewed snapshots add
23 audited results (ten closed) and 580 contract lines only; existing contracts,
axiom sets and the inherited library-level axiom list are unchanged. There are
370 audited results (72 closed). The regression target passed and the
completeness gate intentionally fails with 434 missing declarations. Normal
assumption and contract comparison gates also finished with exit 0 at 370
results (72 closed), without rewriting snapshots. The clean Nix result
certifies only 91 jets.

## Shared lt/le comparisons at all arithmetic widths

`lt_8/16/32/64` and `le_8/16/32/64` now have complete C-call proofs
against the canonical subtraction-borrow and negated swapped-comparison
programs. Shared specification lemmas connect their actual Simplicity
compositions to numeric comparisons. Operation-parameterized execution and
layout adapters retain signed byte promotions and unsigned wide comparisons,
derive both readers and the bit writer, and discharge return and local cleanup
from initial-only contracts at arbitrary valid cursors and word crossings.

The integrated check with exact AST regeneration finished with exit 0 at
107/533 and 78 public modules, including negative tests. Reviewed snapshots
add 29 audited results (11 closed) and 483 contract lines only; existing
contracts, assumption sets and the inherited library-level axiom list are
unchanged. Normal comparison gates passed at 399 results (83 closed), without
rewriting snapshots. The regression target passed; the completeness gate
intentionally fails with 426 missing declarations. The clean Nix result
certifies only the earlier immutable 91-jet snapshot.

## Zero/one tests at all arithmetic widths

`is_zero_8/16/32/64` and `is_one_8/16/32/64` now have complete C-call
proofs against their literal canonical compositions: negated some, and
decrement followed by payload is_zero. A symbolic bridge reuses the some
recursion and signed decrement balance, with a modulus-at-least-two bound to
handle the wrapping zero input. Shared byte/wide execution and initial-only
layout adapters retain the actual equality comparisons and promotions, and
derive reads, bit writes, return and local cleanup. Public specs include
arbitrary valid cursors, crossings and unrelated output bits.

The integrated check with exact AST regeneration finished with exit 0 at
115/533 and 83 public modules, including negative tests. Reviewed snapshots
add 28 audited results (ten closed) and 423 contract lines only; previous
contracts, assumption sets and the inherited library-level axiom list are
unchanged. Normal comparison gates passed at 427 results (93 closed), without
rewriting snapshots. The regression target passed. The completeness gate
intentionally fails with 418 missing declarations; this is progress, not
completion. The clean Nix result still certifies only the 91-jet snapshot.

## Minimum/maximum selection at all arithmetic widths

`min_8/16/32/64` and `max_8/16/32/64` now have complete C-call proofs
against the literal canonical le-and-input followed by conditional projections.
The shared strict-selection bridge accounts for the C's `<` versus canonical
`<=`, including equal inputs, using word-value injectivity. Byte/wide execution
adapters follow the generated `_t'3` assignments and writer calls, retaining
byte promotions and the uchar argument cast. All reads, writes, return and
local cleanup are derived from initial-only arbitrary-layout contracts.

The integrated check with exact AST regeneration finished with exit 0 at
123/533 and 86 public modules, including negative tests. Reviewed snapshots
add 25 audited results (seven closed) and 495 contract lines only; existing
contracts, assumption sets and the inherited library-level axiom list are
unchanged. Normal comparison gates passed at 452 results (100 closed), without
rewriting snapshots. The regression target passed; the completeness gate
intentionally fails with 410 missing declarations. The clean Nix result
still certifies only the 91-jet snapshot.

## Median selection at all arithmetic widths

`median_8/16/32/64` have complete C-call proofs against the literal canonical
nested min/max composition. A shared symbolic bridge connects that composition
to the C's five-comparison decision tree, including ties. The control adapter
retains every generated identity cast; the byte and wide adapters discharge
their actual promotions and casts. Initial-only layout contracts derive three
readers, the writer, return and local cleanup, including arbitrary valid
cursors, crossings and unrelated output contents.

The integrated check with exact AST regeneration finished with exit 0 at
127/533 and 90 public modules, including negative tests. Reviewed snapshots
add 24 audited results (six closed) and 580 contract lines only; previous
contracts, assumption sets and the inherited library-level axiom list are
unchanged. Normal comparison gates passed at 476 results (106 closed), without
rewriting snapshots. The regression target passed; the completeness gate
intentionally fails with 406 missing declarations. The clean Nix result
still certifies only the earlier immutable 91-jet snapshot.

## Non-wrapping forwardBits helper

`jet_forwardBits_layout.v` proves the complete generated `forwardBits` call
from initial frame fields, writable cursor access and non-negative,
non-wrapping cursor arithmetic. It derives the actual store, updated frame
fields, preservation outside the cursor field, permissions and valid blocks.
The helper is included in both project manifests but does not add jet coverage.

An explicit source compilation and direct `coqchk` both finished with exit 0.
The checker reports no type-in-type, unsafe (co)fixpoints or assumed positivity;
its library-level axioms are a subset of the existing allowlist. The complete
helper theorem's `Print Assumptions` reports only the existing six inherited
axioms (classical choice, classical logic, functional extensionality and the
CompCert external/inline-assembly semantics), not a new correctness axiom.

## Streaming-jet separation interface

`jet_context_separated.v` supplies an initial-only local interface for streaming
jets, whose C implementations may write before consuming all input. Its buffer
separation follows formally from the existing represented-caller invariants;
the contextual replacement theorem has the same premises and conclusion as
`jet_context`. Shared input/output cell blocks remain permitted. Existing
arithmetic contracts and proofs are unchanged and imply the new interface.
This supplies infrastructure only: coverage remains 127/533, with 406 missing.

Explicit source compilation and direct `coqchk` passed. The integrated run
finished with exit 0, including kernel checking on 92 public modules, negative
tests and exact AST regeneration. Its assumption and contract snapshots were
reviewed before acceptance.
The nine added audited results include four closed proofs and use only inherited
axioms. Existing per-result assumption sets and the library-level allowlist are
unchanged. Loading the generated AST as a contract-definition module also changes
the printer's `jets.` qualifications and line wrapping; comparison after those
printing differences confirms that existing contract contents are unchanged.
Normal snapshot-comparison gates also finished with exit 0 at 485 audited
results (110 closed), without update mode.

The clean Nix build started from immutable source
`/nix/store/mm52rc5c1msa381k0wifrqgj0v8rk979-source` and derivation
`/nix/store/j0s7vnj4mqq6cjjq05r5gzy72dqf3fdv-Simplicity-coq-jets-0.0.0.drv`.
It contains the 127-jet median proofs and forwardBits helper, not the subsequent
separated-call interface. The clean build finished with exit 0, including kernel
checking on 90 public modules, normal assumption/contract comparisons and gate
negative tests. Its installed result is
`/nix/store/5cdvfbk7qg0vfrdxbnxy75kjn57067af-Simplicity-coq-jets-0.0.0`.

## copyBits wrapper composition (not jet coverage)

`jet_copyBits_exec.v` proves the actual wrapper's zero-count call without any
memory effects. Its nonzero composition theorem includes function entry, the
helper call, cursor read/store and return/free semantics. A further theorem
derives the cursor store and its framing from fields and writable access in the
helper's resulting memory. These INTERNAL results still require execution of
`copyBitsHelper` and preservation of its destination cursor. They are not an
initial-only copy contract and do not establish any projection jet equivalence.

Explicit source compilation and direct `coqchk` finished with exit 0, with no
type-in-type, unsafe (co)fixpoints or assumed positivity, and no library-level
axioms beyond the inherited allowlist. The module is registered in both build
manifests; the preceding 92-module integrated run does not certify this later
addition. The next complete projection proof must discharge the helper's actual
partial-word stores, aligned memcpy/loop behavior and preservation obligations.

## First copyBitsHelper return branch (not jet coverage)

`jet_copyBits_helper_exec.v` proves the actual generated initialization prefix
and the complete helper call for `0 < n <= src_shift < dst_shift`. The final
theorem `eval_copy_helper_short_left` has only initial-state premises: frame
fields and non-wrapping bounds, separated source/destination word loads, and
writable destination access. It derives both stores and source-load preservation
after clearing the destination. It proves the exact resulting word, preservation
of the output frame fields, outside-word loads, permissions and valid blocks.
Output contents need not be zero-initialized.

Explicit source compilation and direct `coqchk` finished with exit 0. Its
assumptions are the same six inherited library-level assumptions as the
existing execution helpers; no new axioms or proof escapes were introduced.
It is registered in both build manifests, but is not a public jet theorem and
does not increase the 127-jet coverage. Other partial-word paths, crossings,
aligned memcpy and loop behavior remain to be proved and composed with the
wrapper before adding projection coverage. The clean Nix build above predates
this module and does not certify it.

## Both short-copy paths and the actual wrapper (not jet coverage)

`jet_copyBits_helper_right.v` proves the second partial-word return path,
`src_shift >= dst_shift > 0`, `n <= dst_shift`, from initial memory. Its
clear/store/framing derivation is shared with the first path through the
INTERNAL `eval_copy_helper_partial_from_tail`. Both branch theorems discharge
that lemma's execution premise rather than exposing it as a final precondition.

`jet_copyBits_short_exec.v:eval_copyBits_short` combines the paths under
`0 < n <= src_shift`, `n <= dst_shift`, executes the actual wrapper, and derives
its cursor store from initial writable access. Its postcondition includes the
exact stored word, destination fields at `cursor - n`, unchanged loads outside
the destination word and cursor field, and preserved permissions/valid blocks.
`jet_copyBits_short_word.v` proves symbolic, width-independent bit observations
of those actual stored values. No enumeration or zero-output assumption is used.

The updated audit adds 40 helper results and 30 transparent definitions,
including the previously direct-checked wrapper module. The existing assumption
and contract records are unchanged, as is the kernel's inherited axiom allowlist.
Kernel checking has passed on 97 audited modules; the updated snapshots contain
525 results, 128 closed. Initially aligned destinations and input/output
crossings are not covered by these short-copy contracts. Coverage remains
127/533, with all 36 projection jets still outstanding. The clean Nix build
above predates these additions.

The integrated `check-jets.sh --update-expected --ast` run finished with exit 0,
including proof scanning, complete-inventory tests, build, 97-module kernel
checking, assumption/contract updates, gate negative tests and regenerated-AST
comparison. Snapshot review found only the new records/definitions; previous
contracts and per-result assumption sets were not changed.

## Short-copy frame cells (not jet coverage)

`jet_copyBits_short_cells.v:eval_copyBits_short_layout` connects the actual
wrapper to `frame_input_cells_at` / `frame_output_cells_at`. It derives the
source word and address bounds from the logical input's first cell and the
destination's access/store facts from `write_frame_at`. It proves equal output
cells, preserved written prefix, updated frame fields and load/permission/block
framing. Undefined input cells are supported without assuming their physical
bit values. Its restrictions remain explicit: a positive count that fits in
both current words, a partial destination word and separated source/destination
word ranges. It is not a public projection equivalence proof.

The source compiled with exit 0; direct `coqchk -silent -o` also finished with
exit 0, the existing library-level axiom set and no unsafe kernel features.
`Print Assumptions` on its eight results introduced no new assumptions; the
complete layout execution result inherits the same six Coq/CompCert assumptions
as the preceding helpers. Both build manifests include it. The 97-module
integrated run above predates this later module; its checks are direct, not
claimed as part of that run or the earlier clean Nix build.

The normal assumption/contract comparisons subsequently finished with exit 0
(525 audited results, 128 closed), as did the regression build and the ordinary
build after registering the cell module. The completion-mode coverage check
still exits 1 intentionally: 406 declared jets have no equivalence proof yet.

## Aligned destination: the first loop return (not jet coverage)

`jet_copyBits_loop_exec.v` proves the actual generated loop's initial fill and
short return, including its `Sskip` prefix and `Sloop` return semantics. The
initial-only `eval_copy_helper_aligned_short` derives a complete helper call
when the destination is aligned, the source is partial and the count fits in
the source word. It derives its single store from writable access and proves
the exact resulting word, destination fields and memory framing. Since its
source read precedes the store, no cell-word separation premise is needed.

Explicit source compilation and direct `coqchk -silent -o` finished with exit
0, the unchanged inherited library axiom set and no unsafe kernel features.
Both build manifests include the module. This direct check is not part of the
preceding 97-module integrated run and adds no public jet coverage.

The actual aligned-source branch calls a separately declared
`EF_external "memcpy"`; it is not the CompCert `EF_memcpy` builtin. A builtin
memcpy proof cannot discharge that external call. A verified linking/model
solution remains necessary before proving every projection layout; the C
source and generated AST have not been replaced to assume away this case.

## Aligned short-copy cells and integrated audit (not jet coverage)

`jet_copyBits_aligned_short.v:eval_copyBits_aligned_short_layout` proves the
complete actual wrapper call from logical input cells and `write_frame_at`
when the destination is aligned, the source is partial and the positive count
fits in its current word. It derives every helper/store/cursor obligation and
proves equal output cells, prefix preservation, updated fields, unchanged loads
outside the destination word/cursor field, and preserved permissions/blocks.
Undefined cells and overlapping cell words are supported. This is an explicit
branch contract, not a full projection-jet equivalence theorem.

The integrated `check-jets.sh --update-expected --ast` run finished with exit 0
on 100 audited modules, including the previously directly checked short-cell
module. Assumptions now cover 548 results, 138 closed. The snapshot diff adds
only 23 new results and seven helper definitions; previous contracts and
assumption sets, and the inherited kernel axiom allowlist, are unchanged.
Proof scanning, complete-inventory tests, kernel checking, negative tests and
regenerated-AST comparison all passed. Public jet coverage remains 127/533.

## Aligned destination: input-crossing loop return (not jet coverage)

`jet_copyBits_loop_crossing.v:eval_copy_helper_aligned_full` proves the actual
second return of the first loop iteration, for `src_shift < n <= 64` with an
aligned destination and partial source. It derives both stores from initial
writable access and preserves the next-source-word load after the first store
using initial word separation. Its complete helper call includes the actual
prefix, loop selection, both fill statements, return and function boundary.
The postcondition gives the exact joined word and metadata/load/permission/block
framing; no intermediate execution/store premise survives. It does not prove
multi-iteration copying or the external memcpy branch.

Explicit source compilation and direct `coqchk -silent -o` finished with exit
0 and the unchanged library-level axiom set, with no unsafe kernel features.
The initial-only theorem inherits the same six assumptions as the other
execution helpers. Both build manifests include it. This later module was not
part of the preceding 100-module integrated run. Normal comparisons for that
run subsequently passed on 548 audited results, 138 closed.

## Partial source and aligned destination: logical crossing contract

`jet_copyBits_aligned_crossing.v` derives current/next source loads and bounds
from logical cells, executes the actual crossing helper and wrapper, and
proves equal output cells, prefix preservation, cursor update and memory
framing. Its unified `eval_copyBits_aligned_partial_source_layout` covers every
positive count up to 64 for a partial source and aligned destination. Next-word
separation is needed only for a crossing, and undefined cells are supported.
There are no intermediate execution or store premises in either layout theorem.

Explicit source compilation and direct `coqchk -silent -o` finished with exit
0, the unchanged inherited library axiom set and no unsafe kernel features.
Both initial-only layout theorems inherit the same six assumptions as the
other execution helpers. Both build manifests include this module; it was not
part of the preceding 100-module integrated run. Public coverage remains
127/533. Partial-destination continuations and the plain external memcpy model
remain outstanding; no C source or generated AST has been changed.

The subsequent integrated `check-jets.sh --update-expected --ast` run finished
with exit 0 on 102 audited modules. The two crossing modules add 13 results
and four helper definitions to the snapshots; prior records have no deletions
or changes, and the inherited kernel axiom allowlist is unchanged. The source
build, proof/inventory checks, kernel audit, negative gate tests and regenerated
AST comparison all passed. This audit still establishes no new public jet
equivalence beyond the existing 127 entries.

## Input crossing inside a partial output word: actual helper call

`jet_copyBits_partial_crossing.v:eval_copy_helper_partial_cross` derives the
complete actual helper call for `src_shift < n <= dst_shift`: destination
clear, left fill, count/shift/source-pointer updates, right fill and return.
All three stores follow from initial writable access; the source reads after
those stores follow from initial separation for both source words. The result
gives the exact word, unchanged frame fields and memory framing. Internal raw
transition lemmas preserve the actual AST and are reusable by longer paths.

Explicit source compilation and direct `coqchk -silent -o` finished with exit
0, the unchanged inherited library axiom set and no unsafe kernel features.
Both build manifests include this later module; it was not part of the
102-module integrated audit. This helper theorem adds no public jet coverage.

## Partial output word: unified initial-only logical contract

`jet_copyBits_partial_crossing_cells.v` proves the exact bit/cell observations
of the crossing word, including preservation of previously written bits.
`eval_copyBits_partial_cross_layout` derives both input loads/bounds from
logical cells and the complete helper/wrapper call from initial writable
frames. `eval_copyBits_partial_word_layout` combines it with the short path,
covering every `0 < n <= cursor mod 64`. Undefined cells are supported and
next-word separation is required only when the source crosses.

Explicit source compilation and direct `coqchk -silent -o` finished with exit
0, unchanged inherited library axioms and no unsafe kernel features. Both
build manifests include this module. These later partial-word modules were
not part of the 102-module integrated audit. They add no public jet coverage:
continuing past a partial destination word and the external memcpy model
still need proofs before a general projection equivalence can be claimed.

## Word protections derived from represented buffer separation

`jet_copyBits_separation.v` proves source/destination word containment and
`copy_buffers_separated_words`, which derives word-level store/load
disjointness from the existing whole-buffer separation predicate. It applies
at every in-range bit index and supports shared input/output cell blocks.
This closes an interface obligation for future projection contracts without
adding caller restrictions or public jet coverage.

Explicit compilation and direct `coqchk -silent -o` finished with exit 0,
unchanged inherited library axioms and no unsafe kernel features. Both build
manifests include the module. The roadmap records the exact still-unproved
partial-destination continuation states, distinguishing temporary pointer
updates from unchanged stored frame cursors.

## Common right-fill continuation (internal, not an initial contract)

`jet_copyBits_right_advance.v` proves the exact generated suffix shape, its
three temporary updates and the actual right-fill continuation past the
short-return test. The resulting source shift is allowed to be zero, so the
future memcpy obligation is not excluded. Execution still assumes the fill's
load/store facts; this is a reusable raw lemma, not a final helper or jet
contract. The remaining two-word initial-only proof must derive those facts
and execute the loop or appropriate library call.

Explicit compilation and direct `coqchk -silent -o` finished with exit 0,
the unchanged inherited library axiom set and no unsafe kernel features.
Both build manifests include this later module; it is not in the 105-module
public audit list yet. Public jet coverage remains 127/533.

## Integrated audit of partial-word crossings and buffer protections

The expanded `check-jets.sh --update-expected --ast` run finished with exit 0
on 105 public-audit modules. It adds 18 audited results and three helper
definitions: the partial-crossing helper, its cell contracts and the word
separation bridge. There are now 579 audited results, 150 closed. Reviewed
snapshot diffs contain only additions; all previous contracts/assumption sets
and the inherited kernel axiom allowlist are unchanged. Source builds,
proof/inventory checks, kernel checking, negative gate tests and regenerated
AST comparison passed. The normal contract comparison also passed.

The later right-advance module has separate compilation/kernel-check evidence
as recorded above and is registered in both build manifests, but was not in
this integrated public-audit set. The every-jet coverage check still exits 1:
127/533 jets have proof entries and 406 remain missing. These copy contracts
are verified intermediate progress, not additional individual jet equivalences.

## Both word crossings, smaller source shift: complete initial helper call

`jet_copyBits_two_words_left_exec.v` composes the actual clear/left/right
partial fills and both temporary advances with the actual loop choice and
first return. `jet_copyBits_two_words_left.v:eval_copy_helper_two_left`
discharges all intermediate premises from initial memory: four stores follow
from writable access to both destination words, and source reads follow from
initial separation from the first destination word. The final store preserves
the completed first word and the destination metadata. The theorem proves
both exact word values and framing outside the two-word interval, preserving
permissions and valid blocks. It covers `src_shift < dst_shift < n <= 64`.

Explicit compilation and direct `coqchk -silent -o` finished with exit 0,
the unchanged inherited library axiom set and no unsafe kernel features.
Both build manifests include these modules. These later modules were not in
the 105-module integrated public audit. They are helper progress only; the
other partial-destination continuation and external memcpy model remain.

## Both crossings: initial-only logical wrapper contract for the left case

`jet_copyBits_two_words_left_cells.v:eval_copyBits_two_left_layout` derives
the source loads/bounds, destination accesses and word protections from
logical cells, `write_frame_at` and existing whole-buffer separation. It
executes the actual helper/wrapper and proves equal output cells, including
undefined cells, prefix preservation, cursor update and framing outside the
two-word output interval and cursor field. Crossing-position/address lemmas
are reusable for the other partial-destination branch. No execution/store
premise remains in this layout theorem.

Explicit compilation and direct `coqchk -silent -o` finished with exit 0,
the unchanged inherited library axiom set and no unsafe kernel features.
Both build manifests include the module. The initial helper and layout
theorems inherit the same six assumptions as previous execution helpers.
These later modules are not part of the preceding 105-module integrated run.
Public coverage remains 127/533; remaining layouts must still be handled.

## Destination-only word crossing: actual initial helper call

`jet_copyBits_two_words_right_exec.v` executes the actual clear/right partial
prefix and temporary advance before a supplied actual loop. The initial-only
`jet_copyBits_two_words_right_short.v:eval_copy_helper_two_right_short`
derives that loop and all three stores for `0 < dst_shift < n <= src_shift`.
It preserves the source read across the preceding stores using initial word
separation, including initially aligned sources. It proves both exact words,
unchanged destination fields and framing outside the two-word interval.

Explicit compilation and direct `coqchk -silent -o` finished with exit 0,
unchanged inherited library axioms and no unsafe kernel features. Both build
manifests include these later modules; they are not in the 109-module public
audit set currently being checked. This adds no public jet coverage.

The 109-module integrated `check-jets.sh --update-expected --ast` run has now
finished with exit 0. It adds 11 results and two helper definitions (including
the earlier right-advance module) to the snapshots: 590 audited results,
153 closed. The reviewed diffs contain only additions; previous contracts,
assumption sets and the inherited kernel axiom allowlist are unchanged.
Source/inventory checks, kernel audit, negative tests and regenerated AST
comparison all passed. Later right-case modules remain outside that run.

## Destination-only crossing: logical wrapper contract

`jet_copyBits_two_words_right_short_cells.v:eval_copyBits_two_right_short_layout`
derives the source word, both output accesses and required word protection
from logical cells, writable frames and whole-buffer separation. It proves
the actual wrapper call, equal output cells (including undefined cells),
prefix/cursor observations and two-word/cursor load/permission/block framing.
It covers initially aligned sources without requiring a nonexistent next
input word or a library call.

Explicit compilation and direct kernel checking finished with exit 0,
unchanged inherited library axioms and no unsafe kernel features. Both build
manifests include this module. It is later than the 109-module public audit
and adds no public jet coverage.

## Larger source shift: both crossings and the second loop return

`jet_copyBits_two_words_right_full.v:eval_copy_helper_two_right_full` derives
the complete actual helper call for `0 < dst_shift < src_shift < n <= 64`.
All four stores follow from initial writable access; the next-source read
after both output words have been modified follows from initial word
protections. It proves both exact words, metadata and memory framing.
`jet_copyBits_two_words_right_full_cells.v:eval_copyBits_two_right_full_layout`
derives these accesses/protections from logical cells, writable frames and
whole-buffer separation, then proves the actual wrapper call, equal cells,
prefix/cursor observations and two-word/cursor framing. Undefined cells are
supported and no intermediate execution/store premise remains.

Explicit compilation and direct kernel checking finished with exit 0,
unchanged inherited library axioms and no unsafe kernel features. Both build
manifests include the modules; they are later than the 109-module audit.
Their branch contracts add no public jet coverage: plain external memcpy and
the final canonical projection calls still need proving.

## Uniform positive small-copy contract outside the external memcpy paths

`jet_copyBits_small_layout.v:eval_copyBits_small_no_memcpy_layout` composes
all branch contracts for every positive count up to 64. It proves the actual
wrapper, equal cells, prefix/cursor observations, permissions/valid blocks
and a uniform output footprint whose low endpoint is
`outedge + 8 * ((cursor - n) / 64)`. Three closed arithmetic lemmas reconcile
the individual one-word/two-word footprints.

The explicit `~ copy_small_memcpy_case` premise excludes two still-required
paths: initially aligned source/destination, and a partial-destination
continuation with equal initial shifts. No library behavior is assumed.
This is not full copyBits correctness or a full projection-jet theorem.
The external model and final canonical jet calls remain outstanding.

Explicit compilation and direct `coqchk -silent -o` finished with exit 0,
unchanged inherited library axioms and no unsafe kernel features. Both build
manifests include this later module; it is not in the 109-module audit.

## Expanded small-copy audit (2026-10-02)

The complete `check-jets.sh --update-expected --ast` run finished with exit 0
on 115 public-audit modules: 605 audited results, 157 closed. It includes the
right-case branch modules, their logical wrapper contracts and the unified
positive small-copy contract excluding the two actual external memcpy paths.
The reviewed snapshots add only 15 results and two helper definitions;
previous theorem contracts, assumption sets and the inherited kernel axiom
allowlist are unchanged. Negative tests and byte-identical AST regeneration
passed; the subsequent normal public-contract comparison also passed.
Public coverage remains 127/533: these are helper results, not new jets.

## multiply_8/16/32 verification (2026-10-02)

The five multiplication modules were explicitly compiled and independently
kernel checked with exit 0. The subsequent complete
`check-jets.sh --update-expected --ast` run also finished with exit 0:
120 public-audit modules, 630 audited results, 166 closed. Reviewed snapshots
add only 25 results and 13 definitions; all previous contracts/assumption sets
and the inherited kernel axiom allowlist are unchanged. The assumption sets
of the new local specs contain only the existing six Coq/CompCert assumptions;
the shared numeric bridges are closed. Context/call guarantees retain the
existing external-call-properties assumptions. No new axioms or execution
premises were added to the final jet contracts.

Coverage/inventory tests, negative gate tests and byte-identical AST
regeneration passed. A subsequent normal public-contract comparison passed,
as did the optional regression target. Coverage is now 130/533, with 403
remaining; `jet-coverage.py --require-complete` still fails as intended.
The earlier clean Nix reproduction covers its recorded 127-jet revision, not
these later modules. No newer clean Nix or remote CI run is claimed.

## Later checked representation infrastructure

`jet_projection_cells.v` and `jet_full_multiply_word.v` were explicitly
compiled and directly kernel checked with exit 0, unchanged inherited library
axioms and no unsafe kernel features. Both build manifests include them.
The projection size/encoding/buffer-slice lemmas and full-multiply carrier
bridge are closed; logical input-cell slicing/encoding lemmas inherit the
existing four classical Coq assumptions through the encoding layer.
These two modules were added after the 120-module integrated run. Their ten
results were not in that run's public assumption/type snapshots. They add no
public jet coverage. The expanded run below audits them and the full-multiply
jet execution consumers; final projection execution consumers remain open.

## full_multiply_8/16/32 verification (2026-10-02)

All four execution/layout modules were explicitly compiled and independently
kernel checked with exit 0. The complete
`check-jets.sh --update-expected --ast` run also finished with exit 0:
126 public-audit modules, 661 audited results, 177 closed. The reviewed snapshots
add only 31 results and 13 definitions, including the ten preceding helper
results. All previous contracts and assumption sets, and the inherited kernel
axiom allowlist, are unchanged. The three new local specs retain only the
existing six Coq/CompCert assumptions; the shared carrier bridge is closed.
Context/call guarantees retain the existing external-call-properties assumptions.

Inventory/coverage tests, negative gate tests and byte-identical AST regeneration
passed. Coverage is 133/533, with 400 remaining. The earlier clean Nix reproduction
does not cover these later modules; no newer clean Nix or remote CI is claimed.

## verify success/failure verification (2026-10-02)

The four assertion/partial-contract/verify modules were explicitly compiled
and independently kernel checked with exit 0. The complete
`check-jets.sh --update-expected --ast` run finished with exit 0:
130 public-audit modules, 669 audited results, 180 closed. Reviewed snapshots
add only eight results and six definitions, including the partial contract,
canonical assertion program/hash and existing assertion interpretation.
All prior theorem types, assumption sets and the kernel axiom allowlist are
unchanged. The option semantics and parametricity bridges are closed; the
new local spec retains the existing six assumptions, and its small-step
guarantees retain the existing external-call-properties assumptions.

Coverage tests now explicitly exercise partial exact-function contracts,
rejecting helper and wrong-function entries. These tests, negative gates and
byte-identical AST regeneration passed. Coverage is 134/533, with 399 remaining.
No additional ABI/build, clean Nix, remote CI, or assertion Bit Machine context
translation claim is made by this verification.

## parse_lock verification (2026-10-02)

The three timelock/specification/execution/layout modules were explicitly
compiled and independently kernel checked with exit 0. The complete
`check-jets.sh --update-expected --ast` run finished with exit 0:
133 public-audit modules, 681 audited results, 184 closed. Reviewed snapshots
add only 12 results and five definitions; all previous contracts, assumption
sets and the kernel axiom allowlist are unchanged. The four new canonical
specification/encoding bridges are closed. The local spec retains the existing
six assumptions; context/call guarantees retain their existing assumptions.

Inventory/coverage tests, negative gates, byte-identical AST regeneration and
a subsequent normal public-contract comparison passed. Coverage is 135/533,
with 398 remaining. No newer clean Nix or remote CI result is claimed.

## Later checked parse_sequence representation infrastructure

`jet_word_bit_spec.v`, `jet_int64_bit_mask.v` and
`jet_parse_sequence_spec.v` were explicitly compiled and independently kernel
checked with exit 0, the same inherited library-level axiom list and no unsafe
kernel features. All 18 new lemma assumption checks report closed under the
global context. Both project manifests include these modules.

They were added after the 133-module integrated audit; the later expanded
parse_sequence audit below includes their public type/assumption snapshots.
They prove shared projection/mask facts,
the literal canonical parse_sequence term's carrier bridge, and both output
encodings, not by themselves the actual C call. Coverage at that stage stayed
135/533. The next results discharge skipBits and the complete jet lifecycle.

## parse_sequence and skipBits verification (2026-10-02)

The actual skipBits cursor/padding contract and the three parse_sequence
execution/writer/layout modules were explicitly compiled and freshly kernel
checked with exit 0. The complete
`check-jets.sh --update-expected --ast` run also finished with exit 0:
140 public-audit modules, 719 audited results, 205 closed. Snapshots add 38
results and 15 definitions, including the 18 preceding representation results.
Removing these additions reproduces the previous contract and assumption
snapshots byte-for-byte; the inherited kernel axiom list is unchanged.
The complete local spec retains the existing six assumptions. Context/call
guarantees retain their existing external-call-properties assumptions.

Both actual branches are proved from initial frames, including arbitrary
valid cursors/crossings and output contents. Disabled output executes skip17
and establishes physical storage for undefined cells without zero assumptions.
The complete call derives source allocation/copy, read32, flag write/branch,
remaining writes/skipping and local cleanup. Prefix, cursor and memory framing
are preserved. Canonical bit/mask and encoding bridges remain closed.

Inventory/coverage tests, negative gates and byte-identical AST regeneration
passed; the optional regression build and subsequent normal public-contract
comparison passed too. Coverage is 136/533, with 397 remaining. No newer clean
Nix, remote CI, other ABI/build or whole-evaluator result is claimed.

## Later checked full-shift encoding infrastructure

`jet_full_shift_cells.v` was added after the integrated 140-module audit.
Its two width/element-parametric encoding lemmas were explicitly compiled and
freshly kernel checked with exit 0; both assumption checks report closed under
the global context. Both project manifests include the module, but it is not
yet in the public type/assumption snapshots. It supplies canonical serialized
cell preservation for both full-shift directions, not a C-call proof; coverage
remains 136/533. The actual copyBits external memcpy paths remain open.

## Later checked sha256_iv initializer infrastructure

`jet_uint32_array_init.v` and `jet_sha256_iv_init.v` were explicitly compiled
and freshly kernel checked with exit 0 after the integrated 140-module audit.
They prove the actual eight-store C initializer from initial permissions, with
array values, framing and permission/block preservation. The canonical scribe
constant's parametricity, register/digest and cell-encoding bridges are closed.
The complete helper call retains only existing Coq/CompCert assumptions.
Both project manifests include these modules; they are not yet in the public
type/assumption snapshots. The enclosing sha_256_iv jet remains unproved until
the actual write32s loop and full allocation/copy/free lifecycle are composed.
Coverage remains 136/533.

## Later checked write32s serialization infrastructure

`jet_output_sequence_step.v`, `jet_write32s_exec.v` and
`jet_write32s_layout.v` were explicitly compiled from current source; fresh
kernel checking of the layout module and its dependency closure finished with
exit 0 and no unsafe kernel features. The two representation lemmas are
closed; the four memory-composition lemmas use the existing four classical
library assumptions, and the loop/layout contracts retain the existing six
Coq/CompCert assumptions. Both project manifests include the modules. They
are not yet in the public type/assumption snapshots.

The complete write32s helper contract derives every load and writer call from
initial array values and writable-frame permissions. It proves serialized
cells, prefix/cursor/framing and permission/block preservation for arbitrary
initial output contents and valid crossings. This is helper progress, not
yet the enclosing sha_256_iv jet proof; coverage remains 136/533.

## Complete sha_256_iv jet verification (2026-10-02)

`jet_sha256_iv_exec.v` and `jet_sha256_iv_layout.v` were explicitly compiled
from current source and freshly independently kernel checked with exit 0.
`sha256_iv_local_spec` proves the actual complete jet against the canonical
Programs.Sha256.Lib.iv scribe term. Both allocations, source copy, all eight
initializer stores, the actual write32s loop, true return and both frees are
derived from initial permissions. Arbitrary valid cursor crossings and
output contents are retained; prefix, cursor and memory framing are proved.
The local spec and context retain six inherited assumptions; the call-boundary
guarantees retain the existing eight-assumption list.

The complete `check-jets.sh --update-expected --ast` finished with exit 0:
148 public-audit modules, 757 results (222 closed). The snapshots add 38
results and 16 definitions, including the preceding full-shift and array
infrastructure. Removing those additions reproduces all previous contract
and assumption snapshots byte-for-byte. The kernel axiom list is unchanged,
with no unsafe kernel features. Inventory/coverage tests, impossible-premise
and lexical negative gates, and byte-identical AST regeneration all passed.
Coverage is 137/533, with 396 remaining. No newer clean Nix, remote CI,
other ABI/build, compression or whole-evaluator result is claimed.

## Later checked one-bit left-padding family

The four `jet_left_pad_bit{8,_wide}_{exec,layout}.v` modules were explicitly
compiled and freshly kernel checked with exit 0 after the SHA IV integrated
audit. All four canonical local specs retain the existing six assumptions;
the representation bridges are closed. The exact catalog padding recursion
is reused, not replaced with a numerical specification. Each call derives
readBit, payload casts, its writer and the full frame lifecycle from initial
memory, allowing arbitrary output contents and valid cursor crossings.
The four entries bring the ledger to 141/533 (392 remaining). Both project
manifests and public audit lists include these modules.

The expanded `check-jets.sh --update-expected --ast` completed with exit 0:
152 modules, 775 results (225 closed), adding 18 results and three definitions.
Removing those additions reproduces all preceding public contract/assumption
snapshots byte-for-byte; the inherited kernel axiom list is unchanged.
Static/inventory/coverage checks, full build/kernel checking, per-result
assumptions, contracts, impossible-premise/lexical negative gates and
byte-identical AST regeneration passed. The optional regression build also
finished with exit 0. The every-jet completeness gate intentionally exits 1:
392 declared jets still lack proof entries. No clean Nix, other ABI/build or
whole-evaluator claim is added.

## Later checked next-family padding/extension bridges

`jet_pad_bit_spec.v` was explicitly compiled from current source and freshly
kernel checked with exit 0 after the latest integrated audit. All seven
parametricity/byte/wide representation lemmas are closed under the global
context. The canonical recursions and conditional composition are checked
against Programs/Word.hs:129-152 and CoreJets' word1 catalog entries. Exact
width-specific extension payloads are retained. Both project manifests include
the module; it is not yet in public snapshots. These are bridges for upcoming
right-padding/left-extension C consumers, not new implementation-to-spec
proofs. Coverage remains 141/533.

## Later checked complete right-padding family

`jet_bit_word_layout.v` and `jet_right_pad_bit{8,_wide}_{exec,layout}.v`
were explicitly compiled from current source and freshly kernel checked with
exit 0. The shared lifecycle is internal; every concrete local spec discharges
its actual-body and writer/canonical-output contracts. The four local specs
retain only the existing six Coq/CompCert assumptions. Actual promotions,
casts and 7/15/31/63 shift guards are proved. All frame generality is retained.
Both project manifests, public audit lists and coverage entries include these
modules, with the previously checked canonical padding/extension bridges.
Coverage entries are 145/533 (388 remaining); integrated audit is pending.

## Later checked complete one-bit left-extension family

`jet_extend_bit{8,_wide}_{exec,layout}.v` was explicitly compiled from
current source and freshly kernel checked with exit 0 and no unsafe proofs.
All four local-spec assumption
checks retain exactly the existing six Coq/CompCert assumptions. The shared
initial-only lifecycle discharges its internal contracts for each actual
conditional assignment, all-ones constant and cast, including the distinct
signed-int, unsigned-int and unsigned-long carriers. The final specifications
retain the literal canonical conditional padding program. No cursor or
initial-output restrictions were added. Both project manifests and public
audit/coverage lists include the family. Coverage entries are 149/533
(384 remaining). The expanded audit result follows below.

## Integrated padding/extension audit (2026-10-02)

The complete `JOBS=12 check-jets.sh --update-expected --ast` run exited 0:
static/inventory/coverage tests, public build, fresh kernel check of 162
modules, 829 public-result assumption and contract snapshots (239 closed),
negative escape-hatch and impossible-premise tests, and pinned AST regeneration.
The 54 added result snapshots and 24 added definition snapshots cover the
canonical bridges, shared lifecycle and eight right-padding/left-extension
jets. Removing those new entries yields byte-for-byte identical previous
contract and assumption snapshots. The inherited 15 library-level kernel
axioms are unchanged, with no type-in-type, unsafe recursion or assumed
positivity. All eight local specs retain only the existing six assumptions.
The separate regression build also exited 0. Coverage is 149/533, with 384
remaining; the completeness gate is intentionally not satisfied. These are
local checks, not a new clean Nix or remote CI result.

## Later checked read32s and canonical chunk infrastructure

`jet_read32s_exec.v`, `jet_read32s_layout.v` and `jet_word32_chunks.v`
compile from current source and were independently kernel checked with exit
0 and no unsafe proofs. The complete reader call theorem retains the existing
six Coq/CompCert assumptions. The initial-only array-reader contract derives every actual
read32 call and Mint32 store, exact canonical uint32 values, final cursor,
permissions/blocks and loads outside the frame-cursor and array ranges.
No output initialization or cursor-alignment restriction is assumed.
Canonical word chunks supply lengths, encoding equality, injectivity and
per-chunk frame inputs without enumerating word values. These are helper
results, not `eq_256` or hash jet equivalence. Both project manifests and
public result/definition lists include them; the expanded integrated audit
passed as recorded below. Coverage remains 149/533 (384 remaining).

## Integrated array-reader/chunk audit (2026-10-02)

The expanded `JOBS=12 check-jets.sh --update-expected --ast` run exited 0
through all static/inventory/coverage, build, kernel, assumption, contract,
negative-test and AST gates: 165 modules, 843 results (246 closed), adding
14 results and eight definitions. Removing those additions reproduces the
previous contract/assumption snapshots byte-for-byte. The inherited 15
library-level kernel axioms are unchanged; no unsafe proofs were found.
The separate regression build exited 0. These helper results add no jet
coverage: 149/533 are proved, 384 remain, and `--require-complete` exits 1.
No new clean Nix or remote CI result is claimed.

## Complete eq_256 equivalence and integrated audit (2026-10-02)

`jet_eq256_array.v`, `jet_eq256_loop.v`, `jet_eq256_exec.v` and
`jet_eq256_layout.v` compile from current source. A fresh independent kernel
check of the final module exited 0. `eq256_local_spec` proves the complete
actual call against `equality_spec (Word 8)`, including both allocations,
source copy, the 16-read/store array loop, eight comparisons with early
return, actual writeBit call and both local frees. All internal execution,
array and cleanup premises are derived from initial frames. The symbolic
chunk/injectivity bridge retains the literal canonical Generic.eq program;
no exhaustive enumeration, output-zero premise or input/output separation
is used. Context and call-boundary guarantees reuse the generic theorems.

The expanded `JOBS=12 check-jets.sh --update-expected --ast` run exited 0
through static/inventory/coverage, build, kernel, assumption, contract,
negative-test and AST gates: 169 modules, 865 public results (253 closed).
The new snapshots add 22 results and 18 definitions. Removing just those
entries reproduces all prior contract and assumption snapshots byte-for-byte.
The inherited 15 library-level kernel axioms are unchanged; no type-in-type,
unsafe recursion or assumed positivity was found. The final local spec keeps
only the existing six Coq/CompCert assumptions. The separate regression
build exited 0. Coverage is 150/533, with 383 remaining; the completeness
command still exits 1. These are local checks, not new Nix or remote CI checks.

Separately, the staged `jet_extend_word8_loop.v` explicitly compiled and
passed an independent kernel check. It matches and executes the actual
left_extend_8_16/32/64 fill loops. At that milestone its writer-run premise
was internal, not yet derived by complete initial-only jet contracts. It was
not in the 169-module audit or either project manifest/public snapshot and
added no jet coverage. It has since been registered with complete consumers
as described in the roadmap. Its explicit compilation command is:

```sh
env OPAMROOT=/Users/brenorb/.opam-simplicity-root opam exec --switch=simplicity -- \
  bash Coq/build-jets.sh --coqc C/jet_extend_word8_loop.v
```

## Complete left_extend_8 family audit (2026-10-02)

`jet_extend_word8_layout.v` completes the three actual left_extend_8_16/32/64
calls, deriving source allocation/copy, read8/uchar normalization, promoted
signed MSB shift and Boolean cast, fill writes, final payload write and free
from initial frames. `jet_write8_sequence.v` discharges the actual writer-run
premise with canonical cells, prefix and memory preservation. The symbolic
canonical padding/fill/MSB bridges enumerate no input words. Arbitrary valid
cursors, crossings and unrelated output contents are supported without an
original input/output separation requirement. Context/call guarantees reuse
the generic results. Fresh independent kernel and individual assumption
checks exited 0; all three local specs retain the existing six assumptions.

The expanded `JOBS=12 check-jets.sh --update-expected --ast` run exited 0
through every gate: 174 modules, 895 results (265 closed), adding 30 results
and 21 definitions. Removing those additions reproduces all previous theorem
types, definitions and assumption snapshots byte-for-byte. The inherited 15
library-level kernel axioms remain unchanged, with no type-in-type, unsafe
recursion or assumed positivity. Negative escape/impossible-premise tests and
pinned AST regeneration passed. The separate regression build exited 0.
This audit covers 153/533 jets, with 380 remaining; it does not establish
completion, a new clean Nix run or any remote CI result.

The mirrored right-extension source modules and initial-only local specs also
compiled and passed fresh independent kernel/individual assumption checks.
The expanded `JOBS=12 check-jets.sh --update-expected --ast` run exited 0
through every gate: 179 modules, 918 results (275 closed). The five registered
right-family modules add 23 results and 11 definitions. Removing just these
additions reproduces the previous assumption and contract snapshots exactly.
The inherited 15 library-level kernel axioms remain unchanged; no type-in-type,
unsafe recursion or assumed positivity was introduced. Negative tests and
pinned AST regeneration passed. Coverage is 156/533, with 377 remaining.
This is not completion, a new clean Nix check or a remote CI result.

The six wide-input extensions (left/right 16_32, 16_64 and 32_64) compiled
and passed fresh independent kernel checks; their canonical local specs retain
the existing six assumptions and their pure bridges are closed. The expanded
`JOBS=12 check-jets.sh --update-expected --ast` run exited 0 through every
gate on 188 modules / 962 results (287 closed), adding 44 results and 28
definitions. Removing those additions reproduces both previous public
assumption and contract snapshots byte-for-byte. The inherited 15 kernel
axioms are unchanged, with no type-in-type, unsafe recursion or assumed
positivity. Negative tests and pinned AST regeneration passed. The separate
regression build exited 0. Coverage is 162/533, with 371 missing; this is
not completion or a new clean Nix/remote check.

The left_rotate_32/64 canonical consumers now include that shared reader,
helper and count infrastructure. Their source builds and fresh kernels passed.
The expanded `JOBS=12 check-jets.sh --update-expected --ast` run exited 0
through all gates on 197 modules / 1004 results (315 closed), adding 42
results / 23 definitions. Removing just these additions reproduces the older
assumption and contract snapshots byte-for-byte. The 15 inherited kernel axioms
remain unchanged, with no type-in-type, unsafe recursion or assumed positivity.
Negative escape/impossible-premise tests, pinned AST regeneration and the
separate regression build passed. That completed audit covers 164/533 jets.

The right_rotate_32/64 canonical consumers also compiled and passed fresh
kernel and individual assumption checks. Their six registered modules add
20 results / 9 definitions, bringing registered coverage to 166/533 (367
remaining). The expanded `JOBS=12 check-jets.sh --update-expected --ast`
run exited 0 through every gate on 203 modules / 1024 results (326 closed),
including negative fixtures and exact pinned AST regeneration. Removing the
right-family additions reproduces all older assumption and contract snapshots
exactly. The inherited 15 kernel axioms remain unchanged, with no unsafe
recursion, assumed positivity or type-in-type. Pure canonical/machine bridges
are closed; final local specs retain the existing six assumptions. The separate
regression build passed. This is not completion or a new clean Nix/remote check.

Six staged nibble-reader modules (`jet_read4_layout.v`,
`jet_read4_crossing_layout.v`, `jet_read4_layout_total.v`, `jet_read4_word.v`,
`jet_read4_input_word.v`, `jet_read4_wide_sequence.v`) compiled explicitly.
Fresh `--coqchk -silent -o C.jet_read4_input_word` and
`--coqchk -silent -o C.jet_read4_wide_sequence` runs exited 0 on their current dependency closure without
unsafe recursion, assumed positivity or type-in-type. They derive actual
read4 execution, exact unsigned Word4 interpretation and cursor/memory
observations from initial frames, including all crossing cases and a shared
read4-plus-wide reader pipeline with exact carriers. They are
now registered through the complete left/right_rotate_16 consumers,
and add no jet coverage by themselves.

Both canonical rotate_16 local specs compiled and passed fresh independent
kernel checks. The expanded `JOBS=12 check-jets.sh --update-expected --ast`
run exited 0 through every gate on 216 modules / 1061 results (344 closed),
adding 37 results / 17 definitions. Removing those additions reproduces the
203-module baseline's assumptions and public contracts byte-for-byte. The
inherited 15 kernel axioms are unchanged, with no unsafe recursion, assumed
positivity or type-in-type. Negative fixtures, pinned AST regeneration and the
separate regression build passed. This audit covers 168/533 jets (365 missing),
not completion, a clean Nix run or remote CI.

The byte-rotation source proofs now compile through the complete canonical
left/right_rotate_8 local contracts. Individual assumption checks retain the
existing six assumptions, and `rotate8_machine_denotes` is closed. The final
independent kernel check exited 0 with no unsafe recursion, assumed positivity
or type-in-type. Nine modules / 31 results / 17 definitions are registered;
the expanded integrated audit passed. That completed audit covers 170/533 (363
missing). They account explicitly for the signed
right-shift promotion, nibble count, payload cast, helper parameter conversions,
writer cast and complete local-frame lifecycle.

The expanded byte-rotation integrated audit (`4716`) exited 0 through every
gate on 225 modules / 1092 results (361 closed). Removing the 31 added results
and 17 definitions reproduces the 216-module assumptions and public contracts
byte-for-byte. The inherited 15 kernel axioms are unchanged; no unsafe recursion,
assumed positivity or type-in-type was introduced. Negative fixtures, pinned
AST regeneration and the separate regression build passed. This is not
completion or evidence of a clean Nix/remote run.

`C/jet_shift8_expr.v` is now registered through zero-fill shift consumers. Its explicit source
build passed, including exact equality to both generated helper body shapes
and evaluation of their promoted shift, fill and count expressions. Its
fresh independent kernel check also exited 0, without unsafe recursion, assumed
positivity or type-in-type. This infrastructure alone does not prove a shift
jet. `jet_shift8_helper_exec.v` now proves its complete helper calls for both
fill flags through internal reader/writer contracts. The actual zero-fill
wrapper execution and initial-only layout result compile and passed fresh
independent kernel checks. Their canonical program adapters, symbolic machine
bridge and both final local specs also compile and passed a fresh final kernel
check; local specs retain the existing six assumptions and
`shift8_machine_denotes` is closed. Eight modules / 33 results / 24 definitions
are registered; entries are 172/533 (361 missing). The expanded zero-fill-shift
audit (`88262`) exited 0 through all gates on 233 modules / 1125 results.
Negative fixtures and pinned AST regeneration passed. Removing the eight new
modules' 33 results / 24 definitions reproduces the 225-module assumption and
contract snapshots byte-for-byte. This completed audit covers all 172 entries;
it does not complete the every-jet goal.

Control normalization initially timed out at count 7 under direct conversion.
Exposing the byte payload's product structure without case-splitting its bits,
then simplifying before conversion, checks the whole normal form in under a
second with the unchanged 10-second tactic limit. No payload enumeration or
assumed helper result is used. Next derive the fill-input public wrappers and
their canonical fill bridge before counting those jets, then extend widths.

`C/jet_shift8_fill_word.v` is now registered through fill-input consumers. Its source
compiles complement involution and the actual fill-XOR's exact bit and unsigned
representation bridge; its fresh independent kernel check exited 0, with no
unsafe recursion, assumed positivity or type-in-type. Individual representation
and involution assumption checks are closed. It is not a
fill-input jet proof by itself.

Both complete fill-controlled byte shift contracts are now checked in
`C/jet_shift8_with_layout.v`. Their literal canonical fill-program normalization,
exact carrier representation, actual wrapper readBit/cast/helper calls, mixed
13-bit reader sequencing, arbitrary valid output frame and local cleanup are
proved. Every new source compiled; a fresh final independent kernel check
exited 0 with no unsafe recursion, assumed positivity or type-in-type.
The named local specs retain the existing six assumptions. Both exact payload
and decoded canonical bridges are closed. Eight modules / 23 results / five
definitions are registered; coverage entries are 174/533 (359 missing).
The expanded fill-input integrated audit (`36618`) exited 0 through every
gate on 241 modules / 1148 results (392 closed), including negative fixtures
and pinned AST regeneration. Removing only these eight modules' 23 results /
five definitions reproduces the completed 233-module assumption and contract
snapshots at `b557293` byte-for-byte. The 15 inherited kernel axioms are unchanged.
This completed audit covers 174/533 entries and does not complete the goal.

`C/jet_shift_wide_expr.v` is now registered through 16-bit consumers. It proves
the exact generated shapes of all six 16/32/64-bit helpers and evaluates their
scalar shifts, fill XORs and count comparisons, accounting for the three
different mask-constant types and Int64 shifts with Vint counts. Its source
compiled and fresh independent kernel check exited 0 with no unsafe recursion,
assumed positivity or type-in-type.

`C/jet_shift_wide_helper_exec.v` now composes all six generated LP64 helpers
with both fill flags and count branches; `C/jet_shift_wide_exec.v` composes
all six zero-fill wrappers. These contracts retain internal reader/writer
premises, so they do not add coverage on their own. Both complete 16-bit
zero-fill local specs now discharge them through initial frames, via
`jet_shift16_layout_machine.v`, literal `jet_shift16_spec.v`, shared symbolic
`jet_shift_wide_bits.v` and closed `jet_shift16_word.v`.
All eight sources compiled; fresh independent checks, including a final
`C.jet_shift16_layout` kernel check, exited 0 with no unsafe recursion,
assumed positivity or type-in-type. Individual local-spec assumption checks
retain the existing six assumptions; generic branch and decoded canonical
bridges are closed. Eight modules / 27 results / 21 definitions are registered;
entries are 176/533 (357 missing). The expanded integrated audit passed.
Removing the added results/definitions reproduces the `c3c8548` snapshots
byte-for-byte. This completed audit covers 176/533.
Next add fill-controlled 16-bit consumers with a mixed bit/read4/read16
initial-state sequence and low-bit (not false exact truncated-carrier) XOR
bridges, then extend 32/64-bit read8-controlled consumers.

The expanded zero-fill 16-bit audit (`51103`) exited 0 through every gate on
249 modules / 1175 results (404 closed). Negative fixtures and pinned AST
regeneration passed. Removing only the added 27 results / 21 definitions
reproduces the `c3c8548` snapshots byte-for-byte. The inherited 15 kernel axioms
are unchanged. This is not completion of the every-jet goal.

Four fill-consumer helpers are now registered: `jet_shift_wide_fill_word.v`,
`jet_shift16_with_spec.v`, `jet_readBit4_wide_sequence.v` and
`jet_shift16_with_word.v`. Every source compiled and each fresh independent
kernel check exited 0 with no unsafe recursion, assumed positivity or
type-in-type. Individual canonical-normal-form and carrier/value bridge
assumption checks are closed. Reader sequencing derives exact values, the
non-wrapping 1+4+width cursor and memory/perms from initial frames, not assumed
reader executions. The low-bit bridge handles the final XOR without falsely
requiring a truncated intermediate left-shift carrier. Use explicit WordToZ
normal forms when rewriting the nested complement: the outer canonical
complement is observed at j, not the potentially out-of-range j-shift index
of the complemented input.

Both complete fill-controlled 16-bit local specs now compile in
`jet_shift16_with_layout.v`. `jet_shift_wide_with_exec.v` executes all six
actual fill-controlled wrappers through internal calls; the W16 initial-frame
result in `jet_shift16_with_layout_machine.v` discharges all three reads,
helper execution, writing and cleanup. The final specs retain arbitrary valid
cursors/crossings, unrelated output contents and memory framing. Fresh source
and independent kernel checks passed; the named local specs retain the same
six inherited assumptions, and canonical machine/payload bridges are closed.
Seven modules / 20 results / five definitions are registered, bringing entries
to 178/533 (355 missing). The expanded integrated audit (`79864`) exited 0
through every gate on 256 modules / 1195 results (414 closed), including
negative fixtures and pinned AST regeneration. Removing only these 20 results
and five definitions reproduces the `5f45b8c` snapshots byte-for-byte. The
inherited 15 kernel axioms are unchanged. Next use read8-controlled wide
sequences and the checked generic helper for 32/64-bit shifts.

## Complete 32/64-bit variable shifts (2026-10-02)

All eight left/right zero-fill/fill-controlled contracts now compile. Fresh
independent kernel checks of their final modules exited 0 (zero32 `54332`,
zero64 `59036`, fill32 `75562`, fill64 `72093`), checking their dependencies as
well. Named local specs retain the same six inherited assumptions; machine
and payload bridges are closed. Initial-only frame contracts derive copying,
all reads, the actual helper, writing, return and cleanup; arbitrary valid
cursors/crossings and unrelated output contents remain supported.

`jet_shift_byte_layout_machine.v` shares W32/W64 zero-fill execution.
`jet_readBit8_wide_sequence.v` and `jet_shift_byte_with_layout_machine.v` share
fill-controlled execution. Canonical programs use Word8 controls as in
CoreJets, including >=width shifts and continued controls at SingleV.
Only controls/fill flags are enumerated; payloads remain symbolic.

For fill64, `cbn` rewriting exceeded the 180s process deadline. An isolated
four-case check took 7.06s with `cbn`, 0.143s with `lazy` and component-wise
equality. The combined theorem then timed out specifically at `Qed` under
the default 10s limit, not during its tactics. Four separately checked
256-control lemmas solved that final check without increasing the timeout.
Source checking uses the same 180s process deadline; no proof escape is used.

Fifteen modules / 49 results / six definitions are registered, adding eight
jets: 186/533 entries, 347 missing. The expanded integrated audit (`87578`)
exited 0 through all gates on 271 modules / 1244 results (436 closed), including
negative fixtures and pinned AST regeneration. Removing only the newly
registered 49 results / six definitions reproduces the `8ef795b` snapshots
byte-for-byte. The inherited 15 kernel axioms are unchanged. This remains
progress toward, not completion of, every jet.

## Division C-side execution and numeric bridges (2026-10-02)

Seven later modules have current-source coqc exit 0 and fresh independent
kernel checks: `jet_division_value.v`; `jet_division8_expr.v` and
`jet_division8_exec.v`; `jet_division8_layout_machine.v`;
`jet_division_wide_expr.v` and `jet_division_wide_exec.v`;
`jet_division_wide_layout_machine.v`. The final frame checks were `28177`
(byte) and `94879` (wide), checking their dependencies as well. Individual
value and representation assumption checks are closed; the two initial-only
frame theorems retain the same six inherited assumptions. Explicit static
scanning of all seven sources passed.

These theorems establish actual C calls and numeric machine output, not yet
C-to-canonical-Simplicity equivalence. No coverage is added. The byte body
uses signed division after promotion, but input-byte ranges exclude -1 and
the MIN/-1 overflow guard. Z.quot/rem therefore coincide with Z.div/mod.
Wide bodies use unsigned long division. Both zero/nonzero branches are
executed, retaining quotient-zero/remainder-input behavior at divisor zero.
Reader/writer executions, allocation/copy/free and memory framing are derived
from initial contracts; no internal executions are assumed by final frame
theorems. The wide theorem shares W16/W32/W64 and the operation selector.

The modules are now registered (21 results / 19 definitions) in both manifests
and public audit lists, without adding coverage. The expanded helper audit is
complete: session `27757` exited 0 through all gates, negative fixtures and
pinned AST regeneration on 278 modules / 1265 results (447 closed). Removing
only the 21 new results / 19 definitions reproduces the `7e90c02` snapshots
byte-for-byte. The inherited 15 kernel axioms are unchanged.
The prior complete shift audit covers 186/533 jets. The next proof obligation
is the literal Programs.Arith recursive division/normalization bridge, not
another mathematical specification or assumed numeric identity. See
JET_ROADMAP.md for the exact canonical dependency chain.

## Shared canonical full-shift observations (2026-10-02)

`jet_vector_shift_word.v` proves numeric conservation, range and both output
projections of the literal Word.full_left/right_shift1 programs with arbitrary
ToZ base items. `jet_full_shift_spec.v` supplies typed adapters corresponding
to Programs.Word.full_shift when one word is a vector of the other. Transparent
product equalities identify Vector (Word n) m with Word (m+n); a checked
representation induction proves that those casts preserve numeric values.
The adapters are parametric and their value/quotient/remainder observations
are symbolic in both word values and widths.

Current-source coqc and fresh independent kernel checks exited 0 for both
modules (`16239`, `5915`). All 24 new results / six definitions are closed
under the global context; explicit static scans pass. Local source commits
are `473aa63` and `f999311`. These are internal canonical-program bridges,
not new C jet equivalence entries. They support division normalization and
eventual fixed-block full-shift jets; the latter still require actual copyBits
calls, including its currently unproved external memcpy paths.

Both manifests and public lists register these additions. Integrated audit
`76184` exited 0 through all gates, negative fixtures and pinned AST regeneration
on 280 modules / 1289 results (471 closed). Removing only these 24 results /
six definitions reproduces the `723ec34` snapshots byte-for-byte. The inherited
15 kernel axioms are unchanged. Coverage remains 186/533, not goal completion.

## Recursive canonical division normalization (2026-10-02)

`jet_division_shift_step.v` now proves both zero/nonzero guard bounds from
the actual is_zero(leftmost ...) composition. The zero branch permits exact
numerator/divisor shifts without overflow. The nonzero branch derives the
lower bound required by the next smaller block word.

`jet_division_normalize_spec.v` mirrors Programs.Arith.divPreShift/divPostShift
with n = remaining block-word depth and m = outer vector depth. Each successor
casts the unchanged total size from S m+n to m+S n and recursively uses the
promoted vector. Those casts preserve both numeric observations and algebraic
parametricity. Symbolic inductions prove common positive scaling of numerator
and divisor, normalized divisor bound, preserved numerator bound, inverse
scaling of the remainder and identical normalized divisors for pre/post.
`division_plain_input_normalization` derives the entry bounds after prepending
Word.zero for every positive divisor. No payload enumeration or assumed
division identity is used; div3n2n/div2n1n remain the next missing bridges.

Both current sources compile; fresh independent kernel checks `33224` and
`4202` exited 0, with the inherited library axiom set and no unsafe features.
Explicit Print Assumptions checks of all 38 results / ten definitions are
closed, without REPL errors. Explicit static scans pass. Source commits are
`f0aca75`, `b0cbabe` and `6882309`. These are internal canonical-program
observations, not new C jet coverage.

Both manifests and public lists register the two modules. Expanded audit
`13659` exited 0 through all gates, negative fixtures and pinned AST regeneration:
282 modules / 1327 results (509 closed). Removing only these two modules'
38 results / ten definitions reproduces baseline `ef3ec4d` snapshots byte-for-byte;
the 15 inherited kernel axioms are unchanged. Coverage remains 186/533,
and the every-jet goal is active.

## Literal canonical recursive division core (2026-10-02)

`jet_division_core_spec.v` mirrors Programs.Arith.div3n2n through a builder
parameterized by its smaller div2n1n call, allowing structural recursion in
`div2n1n_word_spec`. It retains the approximation's less/equal branches,
overflow case and loop0/loop1/loop2 corrections. `div_mod_word_spec` uses
the exact is_zero branch and pre/core/post composition from CoreJets;
divide/modulo are projections and divides swaps its inputs before modulo.

All programs have checked parametricity. The eight closed bit-input cases
prove the actual base program's valid result and invalid all-ones fallback.
The canonical zero-divisor branch returns (zero,input). Symbolic inductions
prove the literal msb threshold and high-half comparison observations;
`division_plain_input_guard` connects checked normalization to div2n1n's
actual conditions for every positive divisor. No wider payloads are enumerated.

Current-source coqc exited 0, fresh kernel check `79062` exited 0, and explicit
static scanning passes. All 21 results / ten definitions are closed under the
global context, with no REPL errors. This module is still UNREGISTERED; the
normalization audit `13659` has completed, so it may be registered and included in
a subsequent integrated audit before claiming public-audit coverage. It adds
no C jet entries. The remaining obligations are numerical correctness of
the recursive div3n2n approximation/overflow/two correction rounds and the
two div3n2n calls in div2n1n, followed by the generic div_mod bridge and actual
C-call consumers. Preserve the invalid all-ones fallback in the div2n1n result:
it also specifies CoreJets DivMod128_64, not only an internal normalized call.

## Checked recursive division and eight C consumers (2026-10-02)

The previously open approximation, overflow and correction obligations are now
proved in `jet_division_correction_spec.v` and `jet_division_approx_spec.v`.
The recursive contract is discharged for every word depth in
`jet_division_recursive_spec.v`; both wider calls satisfy their input bounds.
`jet_division_result_spec.v` combines this core with checked pre/post scaling,
Euclidean uniqueness and the zero-divisor branch. Its representation theorem
connects the existing C numeric observations to the actual canonical divide
and modulo programs. `div2n1n_invalid_result` preserves the all-ones fallback.

All current sources compile. Fresh kernel checks passed for the corrected
sources: core `89391`, correction `17792`, approximation `76065`, recursion
`19723`, public numeric/representation bridge `34412`, and the complete C-call
consumers `47007`. Earlier approximation check `43094` was on an older compiled
artifact and is NOT evidence for the completed builder theorem; `76065` is its
replacement after current-source coqc exited 0. Explicit scans and assumption
checks pass: canonical helpers are closed, C local/context results retain the
six existing assumptions, and guarantees add only the two existing Events
property assumptions. No admits, new axioms or proof escapes were introduced.

`jet_division_layout.v` proves actual divide/modulo at 8/16/32/64 bits from
initial frames, not post-read states. Arbitrary valid input/output cursors,
word-boundary crossings, pre-existing output contents, zero divisors and exact
memory framing are retained. Public local specs, contextual replacement and
call-boundary guarantees are exported.

Six modules / 68 results / 21 definitions and eight new coverage entries are
registered. Coverage bookkeeping is 194/533 (339 missing). Expanded audit
`28051` finished with exit 0: all gates, negative fixtures and pinned AST
regeneration passed (288 modules / 1395 results, 561 closed). Removing only
the six new modules' assumptions and contract blocks reproduces baseline
`c5e084d` byte-for-byte. All 15 inherited kernel axioms are unchanged. The
updated snapshots have been reviewed and accepted.

Next: actual div_mod calls (two writers), divides calls (swapped operands and
one-bit output), then DivMod128_64 (including invalid input behavior). Reuse
the checked generic canonical bridges; no normalization or arithmetic induction
needs to be repeated. For the seen convertible-type rewrite mismatch, capture
the literal call/guard from the goal and use exact checked contracts, rather
than unfolding large word functions. The every-jet goal remains active.

## Divides and ordered div_mod C consumers (2026-10-02)

The six divides modules compile from current source; fresh kernel checks
`70444` (pure/scalar bridges), `64738` (byte execution), `91259` (byte local
contract) and `41685` (shared wide consumer) passed. The five numeric bridges
are closed. Four local specs and contexts retain only the inherited six
assumptions; guarantees add only the two existing Events properties. Explicit
escape-hatch scans pass. All zero divisors are covered according to the actual
canonical program, not the conflicting nearby Haskell comment.

Six modules / 26 results / 16 definitions and four coverage entries are
registered: 198/533, 335 missing. Integrated audit `24374` finished with exit 0:
all gates, negative fixtures and pinned AST regeneration passed (294 modules /
1421 results, 568 closed). Removing only the six new modules' assumptions and
contract blocks reproduces accepted `f15a9a6` byte-for-byte. All 15 inherited
kernel axioms are unchanged. The reviewed snapshots are accepted; this is the
latest completed integrated audit, covering 198 entries.

Six div_mod modules compile and pass explicit scans/assumption
checks: `jet_divmod_expr.v`, `jet_divmod_representation.v`, byte/wide execution
and byte/wide layout consumers. Fresh kernels `28975`, `75385`, `8206` passed
after current-source coqc. The pair representation is closed; C contracts keep
the inherited assumptions. Actual C writes quotient then remainder. Reuse
`write8_sequence_run_layout` / `write_wide_sequence_run_layout` to derive both
calls and memory framing; do not assume either intermediate call. The four
div_mod entries are registered and included in the expanded audit below.
The next harder jet is DivMod128_64 with its correction-loop helper. In the
pinned LP64 Clight, uint_fast32_t locals/parameters are **tulong**, not tuint;
their 32-bit logical bounds must follow from readers/loop invariants.

## 96/64 correction infrastructure and expanded div_mod audit (2026-10-02)

The six `jet_divmod96_{arith,value,expr,init,step,loop}.v` modules pass
current-source coqc, explicit escape-hatch scans and fresh kernels: numeric
`63181`, scalar/guard execution `81516`, machine initialization `1580`, actual
memory correction step `82032`, and loop composition `20160`. Explicit
assumption checks find closed numeric/initialization facts and only inherited
assumptions in C statement execution. The loop-take rule still requires a
checked tail execution; the whole helper must discharge it with the proved
two-correction bound and derive every store from permissions.

Twelve modules / 48 results / 25 definitions and four div_mod coverage entries
are registered. Inventory bookkeeping: 202/533, 331 missing. Full audit `64579`
is running against accepted `c27d813`; freeze registered proof sources,
manifests and public lists. Expected totals: 306 modules / 1469 results. Do not
accept snapshots before terminal exit 0, all gates/negative fixtures and pinned
AST regeneration. Removing only C.jet_divmod* assumptions and new result blocks
from `exec_divmod8_choose` to `frame_fields`, plus definitions from
`divmod8_choose` onward, should reproduce the baseline byte-for-byte. Retain all
15 inherited kernel axioms. Last completed integrated audit: `24374`, 198 jets.

Next: the memory-aware actual `f_div_mod_96_64` call, then the public
`f_simplicity_div_mod_128_64` call. The roadmap records the precise invariant
and branch-specific execution plan; none of these helper results is a new
jet coverage entry. Canonical DivMod128_64 uses `div2n1n_word_spec 6`, not the
ordinary div_mod program. No canonical division induction needs restarting.

## Accepted 128/64 infrastructure audit and checked public consumer (2026-10-02)

Integrated audit `97656` completed with terminal exit 0: all gates, negative
fixtures and exact pinned AST regeneration passed on 318 modules / 1511 results
(607 closed). Filtering the eight newly registered modules and their contract
blocks reproduces accepted `b59bef9` byte-for-byte, and all 15 inherited kernel
axioms remain unchanged. Accept the assumption/contract snapshots.

The independently checked `jet_divmod128_{allocate,branch_layout,initial,layout}.v`
consumer chain now derives the complete public jet from original frame contracts.
Current-source coqc, explicit scans/assumption checks and fresh kernels passed
(`18978`, `19483`, `63010`, `64639`). Its local spec, canonical context replacement
and both guarantees have no intermediate execution premises. These four modules /
nine results / four definitions plus the public coverage entry are now registered
(203/533, 330 remaining). Expanded audit `39496` completed with terminal exit 0:
all gates/negative fixtures and exact pinned AST regeneration passed on 322 modules /
1520 results (610 closed). Filtering the four modules' assumptions and their new
contract blocks reproduces accepted `cd7d4ee` byte-for-byte; all 15 inherited kernel
axioms are unchanged. Accept these snapshots; DivMod128_64 is fully integrated.

Ten new multiply64/uint128 modules independently compile, pass scans/assumption
checks and fresh kernels (`59569`, `89699`, `32146`, `34160`, `52025`, `20300`,
`21748`, `99795`, `43991`, `98186`). They include the complete multiply64_local_spec,
context/guarantees and every real helper/store/getter/writer/local-lifecycle
operation. Their 39 results / 27 definitions and public entry are now registered
(204/533, 329 remaining); audit
the expanded 332 modules / 1559 results. None of the private helper facts counts
as a public jet. Continue with the two u128_accum_u64 calls for full_multiply_64.

Expanded multiply64 integration audit `54062` completed with terminal exit 0
through every gate, negative fixtures and pinned AST regeneration: 332 modules /
1559 results (632 closed). Filtering the ten new modules and their contract
blocks reproduces accepted `027ee37` assumptions/contracts byte-for-byte; all
15 global inherited kernel axioms remain unchanged. Accept the snapshots.
multiply_64 is now fully integrated (204/533, 329 remaining). The registered
sources/manifests/public lists are no longer frozen for this finished run.

## Independently checked fullMultiply64 consumer (2026-10-02)

Six new, unregistered modules derive the complete actual full_multiply_64 call:
`jet_u128_accum_{value,layout}.v`, `jet_full_multiply64_{spec,exec,layout}.v` and
`jet_read_wide_quad_layout.v`. The accumulator proves its wrapped-low comparison,
both actual stores and updated-low reload. The pure canonical bridge derives
both fit bounds from Word.fullMultiplier's output range. The public local spec
derives two fresh locals, source copy, four actual readers, multiplication,
two accumulations, write128, true return and cleanup from original general
frame contracts. No fixed cursors, non-crossing or output-zero premise is added.
All source checks/scans passed; both value lemmas and both canonical bridge
lemmas are closed. Public execution/context retain only inherited assumptions.
Fresh kernels passed (`17745`, `1861`, `29082`, `81459`, `62488`, `69092`).
These sources are committed locally but must not be registered while audit
`54062` is live. Register and expand the audit after accepting that run.

Three new, unregistered buffer/context-initialization support modules also
compile and pass fresh kernels (`47693`, `73135`, `50275`).
`jet_buffer_empty_spec.v` ports the literal SingleB/DoubleB bufferEmpty recursion,
with symbolic empty-buffer values and encodings. `jet_sha256_ctx8_init_spec.v`
ports literal buffer63Empty &&& (zero word64 &&& iv), preserving the 830-cell
context type. Both modules' results are closed. `jet_empty_buffer_segment.v`
derives each actual false writeBit and skipBits from initial writable output,
preserving padding contents and deriving writable continuation; it retains
only inherited assumptions. Its two results and the canonical modules' eleven
results add no public coverage. The real write_buffer8 loop, SHA initializer,
struct copies/context writer and public lifecycle remain to be executed.
Together with the six fullMultiply64 modules these nine modules have 29 results /
19 definitions to register after audit `54062` completes (341 modules / 1588
results expected). Only full_multiply64_local_spec adds a public entry.

After accepting multiply64 audit `54062` at `87d0082`, these nine modules /
29 results / 19 definitions and the full_multiply64 public entry are registered
(205/533, 328 remaining). Run the expanded 341-module / 1588-result audit against
that accepted baseline. No SHA context jet is counted by these support modules.

Expanded integration audit is running as session `52561`, accepted baseline
`87d0082`. Freeze all registered sources, manifests and public lists until its
terminal result. Expect 341 modules / 1588 results. After terminal exit 0 through
all gates/negative fixtures/AST, remove the nine new modules from assumptions;
remove theorem blocks beginning at `u128_accum_low_balance` until `frame_fields =`
and definition blocks beginning at `u128_accum_lo =` from contracts. Those filtered
files must reproduce `87d0082` byte-for-byte, with unchanged global kernel axioms.
Do not accept snapshots early or restart a live audit. New unregistered actual
buffer-loop/initializer consumers may be developed while this run finishes.

Audit `52561` subsequently completed with terminal exit 0 through all gates,
negative fixtures and exact pinned AST regeneration (341 modules / 1588 results).
Both prescribed filters reproduce accepted `87d0082` byte-for-byte, and all
15 inherited global kernel axioms are unchanged. Accept these snapshots:
full_multiply_64 is fully integrated (205/533, 328 remaining). Registered sources
and manifests are no longer frozen for this completed run.

Next bounded consumer: actual write_buffer8 with len=0 and n=5. Its two
PRODUCTION assertion guards are constant false; i starts at 32, writes six false
tags with skip counts 256/128/64/32/16/8 and halves down to zero. Reuse the checked
segment continuation/preservation, retaining both actual calls and every loop
comparison/update. Then execute sha256_init's iv initialization, compound-field
stores and actual struct-return copy, compose write_sha256_context's buffer,
write64 and write32s calls with protected context reloads, and derive every public
local allocation/copy/free. The canonical context output is 830 cells, including
510 buffer cells with arbitrary absent-payload contents. Do not count the
canonical bridge or conditional loop adapter as a completed public jet.

## Initial-only empty-buffer writer checked (2026-10-02)

Five additional, unregistered modules now cover the actual empty-buffer helper:
`jet_write_buffer8_empty_{exec,run,call,cells,layout}.v` (22 results / 18 definitions).
The statement adapter executes both disabled production assertions, the actual
initial shift, every loop comparison, false-tag call, skip call, unsigned halving,
loop exit and normal return. The cell bridge is closed. The final
`eval_write_buffer8_empty_layout` derives all six calls from an initial writable
510-cell frame; it assumes no intermediate execution. It produces the literal
canonical bufferEmpty encoding, preserves prefix bits and outside loads, updates
the cursor, and preserves permissions/valid blocks at arbitrary valid crossings.
Fresh kernels passed (`46774`, `18222`, `10826`, `84985`, `36948`), with clean
scans, closed cell lemmas and only the six inherited execution assumptions.

These modules stay unregistered while audit `52561` is live. They add no public
coverage: the SHA context initializer, its struct-return copies, the context
writer and enclosing public lifecycle still need complete execution. The actual
pinned sha256_context field order is output (offset 0), counter (8), block (16),
overflow (80), with total size 88; derive this metadata from the AST rather than
assuming the block precedes the counter. Next compose bufferEmpty, write64 zero
and write32s IV with protected context/array reloads.

The empty-buffer sequence now also derives writable tail space, rather than
only final fields (fresh kernel `58527`). Four further modules complete the
initialized-context writer: `jet_sha256_context_fields.v`,
`jet_write_sha256_context_empty_{exec,layout}.v`, and
`jet_write64_then32s_layout.v`. The actual pinned field offsets/size are checked,
every context reload is protected across the actual output calls, and
`eval_write_sha256_context_empty_layout` derives the whole 830-cell canonical
output from initial context/IV/frame observations. The shared 64-bit-plus-array
writer retains general arrays and output crossings. Fresh kernels passed
(`86717`, `36470`, `85875`, `83260`), scans are clean, the zero-word bridge is
closed, and execution uses only inherited assumptions. These are helper proofs,
not public SHA context coverage: actual initializer stores, struct-return/copy
and enclosing allocation/free remain. The nine new modules have 35 results and
27 definition/type entries for the next expanded audit (350 modules / 1623 results).

Those nine modules / 35 results / 27 definitions/types are now registered;
expanded integration audit `45575` is live against accepted `4ac1e5d`. Freeze
registered sources/manifests/public lists until its terminal result. No new
public jet is claimed (205/533 remains). After terminal exit 0 through all gates,
negative fixtures and AST, filter the nine new module names from assumptions,
the theorem contract blocks from `buffer8_actual_loop_shape` until `frame_fields =`,
and definition/type blocks from `buffer8_actual_loop =` onward. The results must
reproduce `4ac1e5d` byte-for-byte with unchanged inherited global kernel axioms.
Develop the actual initializer/copy/public-lifecycle consumer in new unregistered
modules while this audit runs; do not accept snapshots early.

## Complete public SHA256 context initialization checked (2026-10-02)

Nine further unregistered modules (26 results / 15 definitions) now derive the
complete actual `simplicity_sha_256_ctx_8_init` call against literal
`buffer63Empty &&& (zero word64 &&& iv)`: `jet_sha256_init_zero_exec.v`,
`jet_sha256_init_fields_layout.v`, `jet_struct_copy_loads.v`,
`jet_sha256_init_{exec,layout}.v`, `jet_four_locals.v`, and
`jet_sha256_ctx8_init_{exec,prepare,layout}.v`.
The public theorem derives the caller's four allocations, source copy, nested
initializer's fifth allocation, all 64 byte stores and other field stores,
88-byte struct-return copy, second 88-byte caller copy, complete context writer,
true return and every free. The actual caller cleanup order is context/source/
IV/return-local, checked from `blocks_of_env`. General output cursors/crossings,
arbitrary absent-payload contents and all permitted old-memory framing remain.
No initializer, copy, writer or free execution is a public premise.

All current sources/scans pass. Fresh kernels passed (`90811`, `36683`, `23100`,
`83356`, `92056`, `66316`, `14240`, `37305`, `28479`). Public execution/context
use only six inherited assumptions, call-boundary guarantees add the two inherited
external-call properties, and generic memory-only copy/allocation facts use the
existing four memory assumptions. No axiom allowlist is expanded. The struct
copy is Clight's actual By_copy assignment, not an assumed external memcpy call.
The skill's bounded statement templates and initial-only composition guided this
proof; do not reduce the full open memory/program state.

Commit these proofs locally, but keep them unregistered while audit `45575`
is live. Public coverage stays 205/533 registered/audited, with one additional
public jet independently checked. After accepting that run, register these nine
modules, 26 results, 15 definitions and `sha256_ctx8_init_local_spec` as the exact
public `simplicity_sha_256_ctx_8_init` entry, then run the expanded audit (359
modules / 1649 results, 206/533 registered and 327 remaining). Only this public
theorem adds coverage; all its private support remains infrastructure.

Audit `45575` subsequently completed with terminal exit 0 through every gate,
negative fixture and exact pinned AST regeneration (350 modules / 1623 results,
667 closed). Both prescribed filters reproduce accepted `4ac1e5d` byte-for-byte,
and the inherited global kernel axiom list is unchanged. Accept these helper
snapshots; public coverage remains 205/533, with the completed context-init public
theorem ready for registration. The registered sources/manifests are no longer
frozen for this completed run.

After accepting `45575` at `a77fcf0`, the nine complete context-init modules /
26 results / 15 definitions and exact public coverage entry are registered
(206/533, 327 remaining; 205 fully integrated so far). Run the expanded
359-module / 1649-result audit against that accepted baseline. Helpers do not
count separately, and no context add/finalize/compression result is claimed.

Expanded context-init audit `94007` is live; accepted baseline is `a77fcf0`.
Freeze registered sources, manifests and public lists until terminal completion.
Expect 359 modules / 1649 results. After terminal exit 0 through every gate,
negative fixture and AST, filter the nine new module names from assumptions;
filter theorem blocks from `eval_sha_ctx_local_field` until `frame_fields =`
and definition blocks from `sha_ctx_local_field =` onward. These must reproduce
`a77fcf0` byte-for-byte, with the inherited kernel axiom list unchanged. Do not
restart a live audit or accept its snapshots early. Continue new unregistered
Buffer63 input/reader and present-chunk writer consumers while it runs.

## Byte-array and Buffer63 reader support checked (2026-10-02)

Eight additional unregistered modules / 38 results / 20 definitions are checked:
`jet_read8_input_word_total.v`, `jet_read8s_{exec,layout}.v`, `jet_buffer_input.v`,
`jet_read_buffer8_{exec,present_layout,call,empty_layout}.v`.
They prove symbolic byte reads at arbitrary crossings, the complete actual
byte-array read/store loop from initial memory, canonical vector/chunk cell
decomposition, actual reader branch/update execution, a total present-branch
consumer, and the complete all-absent Buffer63 call. The last consumer derives
the initial length store, six tag reads and forwardBits calls, every halving,
loop termination and normal return, with arbitrary absent-payload contents.
It does not require permissions for the unused output byte-array pointer.

Source builds and explicit scans pass. Fresh independent kernels passed
(`28198`, `78154`, `92789`, `27426`, `13104`, `18415`, `34314`); after moving
the reusable cell-preservation fact to `jet_buffer_input.v`, dependencies were
rebuilt and the fresh combined eight-module check `28720` passed. Inspected
execution assumptions are the existing six, representation/memory facts use
only the inherited memory assumptions, and the global 15-axiom list is unchanged.
No proof escape or new axiom is introduced. Public coverage remains 206/533
registered, 205 fully integrated while `94007` is live. These helpers add no
coverage entries. Do not edit the registered manifest or accept the pending
snapshots before the existing audit terminates successfully.

After accepting `94007`, register all eight modules/results/definitions in
dependency order for the next audit (367 modules / 1687 results; 206 public jets).
The next total reader obligation is arbitrary absent/present Buffer63 mixtures,
including preservation of previously written array bytes and unread input cells
through the byte and length stores. The present-branch initial consumer and
canonical chunk decomposition are ready; the complete empty call is not a
substitute for the arbitrary-buffer result. Then extend the present writer and
compose the actual context reader's overflow/failure behavior before new public
context-add/finalize claims. Continue to honor the compression linking and plain
external memcpy blockers recorded in `C/JET_ROADMAP.md`.

## Context-init audit recovery and arbitrary-chunk contracts (2026-10-03)

On continuation, `94007` returned an unknown process handle and its known shell
PID 340 was absent. No matching audit/negative/AST process remained. The observed
build, 359-module kernel, assumption and contract gates passed, but the old
terminal result after the negative-test start is unavailable; do not invent a
terminal pass. Registered proof sources and manifests remain byte-identical to
registration commit `0ee0bc1`. The prescribed `a77fcf0` snapshot filters and
unchanged global-axiom comparison were checked with exit 0.

Recovery `33472` reruns only the unobserved negative tests and exact pinned AST
regeneration. Its durable output is
`/tmp/jet-audit-recovery.qWC9in/remaining-gates.log`; shell PID 36752, Python gate
PID 36761 were observed live. Poll that exact handle, or inspect its live process
and durable output if the tool handle expires. The success marker `remaining
context-init audit checks passed` is printed only after both commands succeed
under `set -e` (the outer logging pipeline uses `pipefail`). Accept pending
snapshots only once this recovery succeeds; keep registered sources frozen.

Two further unregistered modules now pass source, scan, assumptions and fresh
kernels (`32751`, `8151`): `jet_buffer_chunks.v` shares exact chunk width/capacity,
payload size and previous-byte array framing, and `jet_read_buffer8_tag_layout.v`
derives the actual tag read for either canonical branch while preserving the
payload cells. The support batch is now ten modules / 54 results / 28 definitions
(next integration: 369 modules / 1703 results; no new public coverage). The next
implementation obligation remains the total mixed-chunk loop and complete
arbitrary Buffer63 reader, not a conditional call witness.

Recovery `33472` subsequently returned terminal exit 0: the impossible-premise
and escape-hatch negative fixtures behaved as required, exact pinned Clight
regeneration matched, and the saved success marker is present. Combined with
the observed `94007` build/kernel/assumption/contract gates, this completes
context-init integration (359 modules / 1649 results, 676 closed; 206/533 jets,
327 remaining). Both prescribed filters were rechecked against `a77fcf0` with
exit 0 and the 15 inherited global axioms are unchanged. Accept the two pending
snapshot files. The support batch may now be registered separately; it adds no
public coverage and has not yet passed an integrated audit.

Accepted context-init baseline is now `b941abc`. The ten reader-support modules /
54 results / 28 definitions are registered in both project manifests and the
theorem/definition audits, with no additional coverage row (369 modules / 1703
results; 206 public jets). Static and inventory regression checks pass. Run an
expanded logged audit before accepting helper snapshots. Once running, freeze
these registered sources/manifests until terminal success; new unregistered
mixed-loop consumers may be developed independently.

Expanded reader audit `51817` is live against accepted `b941abc`; its durable
log is `/tmp/jet-reader-audit.NrBOUa/audit.log` (369 modules / 1703 results).
Freeze registered sources/manifests/results/definitions until terminal success.
After all gates, negative fixtures and exact AST regeneration pass, filter the
ten new module names from assumptions. In the contract snapshot remove theorem
blocks from `frame_input_word_at_bit8` until `frame_fields =`, and definition
blocks from `read8s_run =` onward. These must reproduce `b941abc` byte-for-byte,
with unchanged inherited global kernel axioms. Do not accept snapshots early or
restart a verified live run. New unregistered chunk-step/loop consumers may be
developed while this run continues.

## Complete mixed Buffer63 reader checked (2026-10-03)

Three additional unregistered modules / 8 results / 1 definition now derive
the actual mixed-chunk reader step, complete halving loop and full Buffer63 call
from initial canonical cells. `jet_read_buffer8_chunk_layout.v` discharges both
tag/branch executions and the length store; `jet_read_buffer8_loop_layout.v`
preserves previous output bytes and unread cells through arbitrary mixtures;
`jet_read_buffer8_layout.v` derives length initialization and normal return.
Current-source compilation and explicit scans passed, fresh kernels `18859`,
`22733`, `92150` returned exit 0, and Print Assumptions `17020` retains only the
existing six execution assumptions. The inherited global kernel context is
unchanged. These are shared helpers, not additional public jet proofs.

Do not register these consumers until live expanded audit `51817` completes;
its registered sources remain frozen. After acceptance the next reader audit
would contain 372 modules / 1711 results, still 206 public jets. Continue with
the actual write8s loop and present Buffer63 writer, then the context reader's
counter/array observations and all overflow return cases. Public consumers must
derive private block separation from their actual allocations.

Expanded reader audit `51817` subsequently returned terminal exit 0. All gates,
negative fixtures and exact pinned AST regeneration passed; the durable log
ends with `all jet checks passed`. The prescribed ten-module assumption filter
and theorem/definition contract filters reproduce `b941abc` byte-for-byte,
and global kernel axioms are unchanged. Accept the two snapshots: 369 modules /
1703 results, 706 closed; 206/533 public jets, 327 remaining. Registration of
new independently checked consumers can now proceed in a separate batch.

The actual write8s loop and total initial-array consumer are independently
checked in `jet_write8s_{exec,layout}.v` (2 modules / 13 results / 5 definitions).
They retain each Mint8unsigned load, actual uchar argument cast, write8 call,
pointer/count update and normal return. Shared byte-sequence encodings and
prefix/sequence framing avoid duplicating representation machinery. The
canonical word-array wrapper gives literal encoded bytes symbolically. Both
sources compile, the explicit scan passes, fresh kernel `1327` returns exit 0,
and Print Assumptions `93046` shows closed representation facts and only the
existing six execution assumptions. No public coverage is added.

The five independently checked mixed-reader/byte-writer consumer modules are
now registered in dependency order (21 results / 6 definitions), without a
coverage row. The next expanded audit has 374 modules / 1724 results, still
206 public jets, against accepted reader-support baseline `0ddec7c`. Freeze
these sources/manifests while the audit runs. After terminal all-gates success,
filter the five new module names from assumptions. Remove theorem blocks from
`buffer8_read_chunk_src` to `frame_fields =`, and definition blocks from
`buffer8_read_chunk_temps =` onward, to reproduce `0ddec7c` byte-for-byte.
Check unchanged inherited global axioms before accepting generated snapshots.

Expanded consumer audit `13723` is live; its durable log is
`/tmp/jet-buffer-total-audit.Pyk5uy/audit.log`. Its build and 374-module kernel
passed; subsequent gates are not yet accepted. Keep registered files frozen.

Three further unregistered modules / 10 results / 1 definition independently
compile and pass scans, assumptions and fresh kernels `31906`, `13689`.
`jet_output_cells_step.v` recovers writable continuation from a nonempty
canonical output sequence and actual framing, including the partially written
boundary word. `jet_present_buffer_segment.v` derives the true-tag and complete
byte-array writes from initial contracts. `jet_write_buffer8_exec.v` retains
the actual comparison, either branch, pointer/length updates and halving;
its internal branch execution premises must be discharged by total consumers.
Print Assumptions `40586`, `98671` adds no assumptions. These helpers add no
public coverage and remain outside the live integrated audit.

The actual mixed writer's initial-only chunk step and canonical tag-choice
invariant now independently compile in `jet_write_buffer8_chunk_layout.v` and
`jet_buffer_write_choices.v` (2 modules / 8 results / 2 definitions). Both pass
explicit scans and fresh kernels `83151`, `63017`; the complete step retains
the existing six execution assumptions (`99522`) and the three canonical
choice facts are closed. The chunk step derives actual branch/halving execution;
its pure tag invariant is established from the canonical remaining-byte length,
not assumed helper behavior. The complete mixed loop/call remains next.

The complete mixed writer loop and arbitrary Buffer63 call subsequently compile
in `jet_write_buffer8_loop_layout.v` and `jet_write_buffer8_layout.v` (2 modules /
3 results / 1 definition). Explicit scans, fresh kernels `99205`, `6681` and
Print Assumptions pass, without new assumptions. The call consumer derives
every comparison/tag/payload/skip/update, both actual disabled assertion loops,
initial shift and return. It preserves arbitrary padding/earlier output and
writable continuation for remaining SHA-context fields. The seven unregistered
writer-support modules total 21 results / 4 definitions. They are independently
checked helpers, not public coverage and not part of live audit `13723`.

Audit `13723` subsequently returned terminal exit 0: every gate, negative
fixture and exact pinned AST regeneration passed; its durable log ends with
`all jet checks passed`. The prescribed five-module assumption and contract
filters reproduce accepted `0ddec7c` byte-for-byte, with unchanged inherited
kernel axioms. Accept snapshots for 374 modules / 1724 results, 716 closed;
public coverage remains 206/533, 327 missing. The seven independently checked
mixed-writer support modules may now be registered for a separate expanded
audit (381 modules / 1745 results; no public coverage row).

The seven complete mixed-writer support modules / 21 results / 4 definitions
are now registered in dependency order against accepted baseline `9cc50d6`.
Run a logged expanded audit and freeze registered files until terminal success.
After every gate, negative fixture and exact AST check succeeds, filter the
seven new module names from assumptions. Remove theorem blocks from
`output_cells_last_word` to `frame_fields =`, and definition blocks from
`buffer8_write_present_temps =` onward, to reproduce `9cc50d6` byte-for-byte.
Check unchanged inherited global axioms before accepting pending snapshots.

Expanded mixed-writer audit `30018` is live; its durable log is
`/tmp/jet-buffer-writer-audit.EHF7td/audit.log`. Its build and 381-module kernel
passed, but remaining gates and snapshots are not yet accepted. Freeze all
registered sources/manifests/results/definitions until terminal success. Poll
that run, or inspect the live process/durable log if its handle expires; do not
restart a verified live audit.

Two additional unregistered modules / 5 results now derive the general actual
SHA-context writer: `jet_write_sha256_context_exec.v` retains arbitrary counters
and either overflow return; `jet_write_sha256_context_layout.v` discharges every
intermediate buffer/count/state call and reload from initial context fields and
canonical arrays. It gives the exact typed 830-cell output and memory framing,
using shared word32 chunks and closed uint32 encoding bridges. Counter modulo
64 equals canonical buffer length as an initial context-representation
invariant; public consumers must derive that invariant from actual context
construction, not assume helper execution. Both sources compile, explicit scans
pass, fresh kernel `86693` checks both modules with terminal exit 0, and
assumptions retain only the existing six execution axioms. These helpers add
no public coverage and are excluded from live `30018`. Next: actual context
reader initialization, mixed reads, counter/overflow stores and returns,
including the real initialized readonly max-counter global observation and
private local cleanup.

Expanded mixed-writer audit `30018` subsequently returned terminal exit 0:
all gates, negative fixtures and exact pinned AST regeneration passed. The
durable log ends with `all jet checks passed`. Both prescribed snapshot filters
reproduce accepted `9cc50d6` byte-for-byte, and the inherited kernel axiom file
is unchanged. Accept 381 modules / 1745 results, 724 closed, still 206/533 public
jets and 327 missing. The two general context writer modules remain separately
checked and unregistered pending their own expanded integration.

Readonly max-counter provenance now independently compiles in
`jet_readonly_int64.v` and `jet_sha256_max_counter.v` (2 modules / 11 results /
1 definition). A generic CompCert initializer lemma avoids reducing the large
generated environment in an open proof. Its actual program specialization
derives the loaded limit and absence of Writable permissions. Allocation,
stores and private-block frees preserve it; the actual Clight global expression
is evaluated using that observation. Explicit scans and fresh kernel `82450`
pass with terminal exit 0; Print Assumptions `29531` reports only four inherited
classical/extensionality assumptions, no new axioms. This does not yet establish
existence of the whole program's initial memory, context-reader execution, or
any additional public jet. These modules remain unregistered for now.

Register the two general context-writer modules and two readonly-initializer
modules for a separate expanded audit against accepted `dd2b9d7`: 385 modules /
1761 results / 1 added definition, no public coverage rows. Freeze all registered
sources/manifests/results/definitions while it runs. After terminal success for
every gate, negative fixture and exact AST regeneration, remove the four new
module names from assumptions; remove contract theorem blocks beginning at
`call_ctx8_buffer` until `frame_fields =`, and the appended definition block
beginning at `sha256_max_counter_at =`, to reproduce `dd2b9d7` byte-for-byte.
Check unchanged inherited kernel axioms before accepting generated snapshots.

Context/provenance audit `58720` is live; durable log:
`/tmp/jet-context-provenance-audit.8Z2vli/audit.log`. The build and 385-module
kernel passed. Remaining gates and generated snapshots are not yet accepted;
registered sources stay frozen. Accepted baseline for its filters is `dd2b9d7`.

The actual context-reader overflow suffix is independently checked in
`jet_read_sha256_overflow.v` (1 unregistered module / 5 results / 2 definitions).
An exact AST suffix check connects the statement to the generated function.
From writable overflow memory, temp observations and the initialized readonly
global, it derives the actual comparison, byte store, reload and both return
outcomes; it preserves the global invariant. Closed comparison bridges expose
the exact unsigned 2^55 threshold without excluding invalid counts. Current
source, explicit scan and fresh kernel `84510` pass with terminal exit 0.
This is a suffix consumer, not whole function or public equivalence coverage;
the reader's earlier calls, local allocation/free and canonical bridge remain.

The actual counter-reconstruction sequence is independently checked in
`jet_read_sha256_counter.v` (1 unregistered module / 3 results / 2 definitions).
An exact AST selector check fixes the sequence; from the private local length
load, current temp observations and writable counter field it derives the
actual local reload, multiply-by-one, shift, addition and store. It retains
machine wraparound on invalid counts rather than asserting unbounded arithmetic
on all inputs. Source, explicit scan and fresh kernel `43218` pass with terminal
exit 0. Assumptions `99361` reports only the six existing execution assumptions
for both counter and overflow consumers; both threshold bridges are closed
(separately checked with Print Assumptions). No public coverage is added.

Next composition detail: derive private len allocation and all reader calls
from initial frames, not intermediate-execution premises. The existing reader
contracts preserve loads and forward permissions; forward permission
preservation alone does not prove that new Writable permissions are absent.
Do not silently infer the readonly no-Writable invariant from that implication.
Use actual store/alloc/free provenance, strengthen helper permission contracts
with checked proofs when needed, or carry the derived exact global load and
initially established destination/global separation through load framing. The
internal store adapters can be used without their stronger invariant wrappers.
The public theorem must discharge whichever interface is chosen, including
actual overflow failure, function return conversion and private-local cleanup.

The two unregistered reader fragments now also export observation consumers.
The counter consumer no longer requires an irrelevant global invariant; the
overflow consumer uses the exact current global load and destination/global
separation, preserving that load after its actual store. Stronger original
provenance wrappers remain checked. This permits composition with the existing
load-framing interfaces without inferring backwards permission preservation.
Both current sources compile, explicit scans pass, fresh kernel `4982` returns
terminal exit 0, and assumptions `78317` retain only the six existing execution
assumptions. The two modules now have 10 results / 4 definitions; no public
coverage and no change to the frozen live integration.

`jet_sha256_read_local.v` independently checks the actual 8-byte private local,
function entry, fresh-block separation, writable/Freeable local permissions,
old-block framing and readonly provenance. It derives cleanup from Freeable
permissions and provides the real function-boundary adapter, including tbool
return conversion for either result. Body execution and retention of Freeable
permissions remain explicit INTERNAL adapter obligations, not public premises
to leave undischarged. The unregistered module has 5 results / 2 definitions;
source and explicit scan pass; fresh kernel `31575` returned terminal exit 0;
assumptions `84802` retain only the inherited four initialization assumptions
and six execution assumptions as appropriate. No public coverage is added.

`jet_read_sha256_context_exec.v` now independently checks the actual full body
and function-call composition (1 unregistered module / 10 results / 3 definitions).
Closed selectors and metadata connect the generated buffer/count/state calls
to their actual symbols and functions; call adapters preserve the real local
address and temp updates. The full body composes those calls, the private len
reload, actual counter store, output-pointer reload and either overflow return.
The function boundary composes actual entry, that body, tbool conversion and
derived local cleanup. These are INTERNAL adapters: their call and current
memory premises must be derived by an initial-only consumer before claiming
public coverage. Both count outcomes and arbitrary machine count/length values
are retained. Current source, explicit scan and fresh kernel `72171` pass with
terminal exit 0; assumptions `38284` retain only the six existing execution
assumptions. The four unregistered reader modules total 25 results / 9 definitions.

Next: derive `eval_sha256_read_context_composes` premises from the initial
canonical 830-cell frame and private context/output representation. Split the
cells into Buffer63 (510), count (64), state (256); apply the complete buffer,
wide64 and word32-array readers in order, deriving every subsequent load and
writable/Freeable permission via framing and store preservation. Initial
readonly provenance establishes each writable destination's global separation;
load framing then retains the exact global observation without assuming
backwards permission preservation. `allocate_sha256_read_local` derives the
actual private allocation and old-block separation. Preserve its Freeable
permissions through all reads/stores and discharge cleanup through the checked
function boundary. Afterwards add the canonical public callers/specification
bridge; neither body nor helper-call adapters alone are public coverage.

Live audit `58720` has now also passed its assumption and contract gates and
generated snapshots. Both prescribed filters reproduce `dd2b9d7` byte-for-byte;
inherited kernel axioms are unchanged. Negative fixtures and exact AST check
remain live/unobserved; snapshots are NOT accepted yet. Do not restart that
specific live run or modify its frozen registered inputs.

Audit `58720` subsequently returned terminal exit 0: all gates, negative fixtures
and exact pinned AST regeneration passed; its durable log ends with `all jet
checks passed`. Both prescribed filters reproduce `dd2b9d7` byte-for-byte and
inherited kernel axioms are unchanged. Accept 385 modules / 1761 results,
729 closed; public coverage remains 206/533, 327 missing. The four unregistered
reader modules remain independently checked and excluded from this audit.
