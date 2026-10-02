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
