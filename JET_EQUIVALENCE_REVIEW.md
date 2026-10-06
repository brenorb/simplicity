> Historical review of revision `33dc0e5f`, dated 2026-09-30. Its findings
> describe that revision only. For the current inherited-work status, corrections
> and remaining obligations, see [JET_INHERITED_REVIEW.md](Coq/C/JET_INHERITED_REVIEW.md).

# Review of the jet-equivalence development

| | |
| --- | --- |
| Reviewed revision | `33dc0e5f0986b0aa17283364d8dfac0f0c2ca9ba` (`feat/jet-equivalence`, "docs(coq): record the fresh-clone verification") |
| Baseline (mainline) | `91d89bac54e9411281ee3b6e766a0ea20eb0a3d3` (`master`, merge-base; "Merge BlockstreamResearch/Simplicity#347") |
| Delta | 125 commits, 159 files, +51,601 / −1 lines (29,098 of them the generated `Coq/C/jets.v`) |
| Scope | `one_N`, `increment_N`, `add_N` for N = 8, 16, 32, 64 (twelve jets); their Coq proofs, build/CI/Nix integration and documentation |
| Review date | 2026-09-30 |

I read the repository instructions, the auto-memory and the Coq proof-engineering skill
(`~/.codex/skills/coq-proof-engineering/SKILL.md`, `references/clight.md`). I edited no proof,
rewrote no history, pushed nothing and contacted nobody. `jet-proof-review.patch` in the
working tree was left untouched. All builds ran in an isolated `git clone` of 33dc0e5 in the
session scratchpad, against freshly downloaded and checksum-verified dependencies.

---

## 1. Summary assessment

**No correctness defect was found.** The twelve public value theorems, the canonical-encoding
restatements, the local-replacement theorem and the call-boundary guarantees all compile from a
clean clone. `coqchk` accepts the 25 modules with no type-in-type, unsafe fixpoints or assumed
positivity. The per-theorem axiom sets contain only inherited Coq and CompCert axioms. The
committed AST is reproduced byte for byte from the pinned C sources. I checked the statements
against the C sources, the generated Clight, `BitMachine.v`, `Translate.v`, `C/frame.{c,h}` and
`C/eval.c`. They say what the documentation says in substance.

- **Implementation against specification:** each theorem names the right generated function and
  the Simplicity term the library uses for the jet. The C integer typing matches the AST and
  the arithmetic bridges.
- **Execution:** helper calls, allocation, the by-value structure copy, stores, return and
  freeing are derived from initial-memory premises.
- **Representation:** the Bit Machine representation is faithful to `eval.c`. Frame cells get
  the correct bit order, zipper reversal, padding and cursor directions.
- **Context preservation:** `jet_context` connects the actual Clight call to the same abstract
  state that `Translate.Naive.translate_correct` reaches. Noninterference (`bm_separated`) is
  kept distinct from the looser aliasing the value theorems permit.

What the checker does **not** give, and what the documentation understates in places:

1. **Public statements are not pinned.** The assumption gate fixes axiom sets, not statements. A
   public theorem made vacuous passed the full gate in my test (VG-1).
2. **Two restrictive contracts are easy to generalise.** Every public theorem fixes the
   environment argument to `Vundef`, although the evaluator passes a pointer (RC-1). The
   per-jet `*_guarantees` drop the cursor, prefix and framing facts (RC-4).
3. **The VST section understates the obstacle.** VST 2.14's own manual excludes struct
   parameters and struct-copying assignments, and VST proves partial, not total, correctness
   (DE-1). This makes the choice of direct Clight proofs *better* justified than the document
   says.
4. **Nix and CI integration is unexecuted,** and the CI cache is probably ineffective (VG-2,
   DE-5).
5. **There is avoidable duplication:** width-copied modules, 19 modules outside every public
   theorem's dependency closure, and two independent ASTs of the frame helpers (MR-1 to MR-4).

Nothing here establishes whole-evaluator correctness, machine-code correctness, or correctness
of `clightgen`. The development does not claim these either.

---

## 2. Commands executed and results

Host: macOS (Darwin 27.0.0) on arm64, Apple clang 21.0.0. Coq 8.17.1 from the opam switch
`simplicity` (`OPAMROOT=~/.opam-simplicity-root`). Paths: `S` = session scratchpad,
`JET_DEPS=$S/deps` (fresh), `TMPDIR=$S/tmp`.

| # | Command (in `$S/review`, a clean clone at 33dc0e5) | Result |
| --- | --- | --- |
| 1 | `git clone --no-hardlinks <repo> review && git checkout 33dc0e5` | Clean tree, no local modifications |
| 2 | `bash Coq/jet-deps.sh` (empty `JET_DEPS`) | Exit 0, 1 min 13 s wall. CompCert 3.14 (`x86_64-linux`, `LIBRARY_FLOCQ=local`) and the VST sha subset built. Both tarballs matched their pinned SHA-256. The CompCert hash equals the Nix hash in `compcert-opensource.nix` (base64 decoded to `5588747d…af20`) |
| 3 | `bash Coq/jet-sysroot.sh` | Exit 0. The glibc 2.36 `.deb` matched its SHA-256 |
| 4 | `bash Coq/check-jets.sh --ast` | Exit 0, 9 min 02 s wall (718 s user, `make -j18`). All 161 `COQC` steps succeeded (the jet project plus the Simplicity library). `coqchk passed on 25 modules`, with `type-in-type`, `unsafe (co)fixpoints` and `positivity is assumed` all `<none>`. Library axioms equal `jet_coqchk_axioms.expected`. `assumption audit passed: 77 theorems, 10 closed`. `Generated AST matches the committed artifact` |
| 5 | **Negative test A.** In `jet_guarantees.v`, `add64_guarantees := fun (_ : (1 = 2)%nat) => …` (a vacuous premise), then `--coqc` and `audit-jet-assumptions.sh` | **Gate passed** (exit 0, "77 theorems, 10 closed"). A vacuous public theorem is not detected (VG-1) |
| 6 | **Negative test B.** One line `Lemma review_cheat : (1 = 2)%nat. Proof. Admitted.`, used by `add64_guarantees` | The static grep of `check-jets.sh:33` **missed** it. The assumption gate **caught** it (`Unexpected axioms … review_cheat`, exit 1) |
| 7 | **Negative test C.** `Int.repr 255` changed to `254` in the committed `jets.v` (the `add_8` carry constant), then `check-jets-generation.sh` | Detected: `cmp` reported a difference at line 19921, exit 1 |
| 8 | `JET_ASSERTIONS=debug regenerate-jets.sh $S/jets_debug.v`, then comparing the bodies of the 12 jets and 11 helpers | Only `f_writeBit` differs from the PRODUCTION AST (RC-3) |
| 9 | All mutations reverted and the modified module recompiled; `git status --short` in the clone | Clean |

Additional static analysis:

- A dependency-closure computation over `Require` lines from the modules in
  `jet_public_theorems.txt`. It finds 19 jet modules outside every public closure (DE-2, MR-2).
- Grep over all jet sources for `Unset`, `Guard Checking`, `Universe Checking`, `Axiom`,
  `Admitted`, `Hypothesis` and timeout settings. The only `Hypothesis`/`Variable` uses are
  section-local in `jet_bitmachine_rep.v:199-208`, `jet_clight_determinism.v:23-26,164` and
  `jet_exec.v:26,251`, and they are discharged at section end.
  `Set Default Timeout 10` appears in 17 files and `30` in `jet_write_wide_layout.v`, matching
  `JET_BUILD.md:157-161`.

Not executed:

- `nix-build -A coqJets` and the full `coq` derivation: no Nix installation.
- The GitHub Actions jobs.
- AST regeneration on a Linux host.
- The existing `codespell` CI job on the new files. The tool is not installed, and I did not
  download it.

---

## 3. Findings

Severity is the impact on the stated guarantees or on the project: **High**, **Medium**,
**Low**, **Info**. No High finding remains.

### 3.1 Correctness defects

**None found.** Specifically, I found no mismatch in:

- function selection;
- integer types and promotions;
- carry and wraparound;
- bit order, reversal, padding and cursor direction;
- the ranges modified by the jets against `bm_separated`;
- the premises of the public theorems;
- the determinism and call-boundary statements.

Section 4 gives the evidence.

### 3.2 Restrictive contracts

**RC-1 (Medium): the environment argument is fixed to `Vundef` in every public theorem.**

- Where: `jet_bitmachine_rep.v:136-138` (`jet_args`), `jet_bitmachine_rep.v:155`
  (`jet_local_spec`), and every `eval_*_layout_matches_spec`, for example
  `jet_add64_layout.v:26`.
- Problem: the evaluator calls `dag[pc].jet(state.activeWriteFrame, *state.activeReadFrame, env)`
  with a real `txEnv` pointer (`C/eval.c:317`). `Clight2.eval_funcall` with a different argument
  list is a different proposition, so no public theorem applies literally to an evaluator call.
- Why the fix is cheap: `clightgen` removed `(void) env;` entirely (see `f_simplicity_one_8` and
  `f_simplicity_add_8` in `jets.v:19793, 19881`). `function_entry2` only binds `_env` as a
  temporary, which is never read, so the generalisation to `forall env : val` should be
  mechanical.
- Documentation: disclosed in `JET_PROOFS.md:201-202` ("which none of these jets uses"), but the
  consequence for the evaluator is not stated.

**RC-2 (Low): the global environment is the single translation unit.**

- All theorems are over `ge0 = Clight.globalenv prog` (`jet_exec.v:75`), where `prog` holds only
  `frame.c` and `jets.c`.
- The call-boundary results quantify over continuations `k` of *that* program's semantics. An
  evaluator caller (`eval.c`) lives in a different unit, so composing with it needs a separate
  compilation or linking argument (CompCert `Linking`).
- `JET_PROOFS.md` "Remaining boundaries" names whole-evaluator correctness but not this linking
  step explicitly.

**RC-3 (Low): only the PRODUCTION AST is covered.**

- Covering the non-PRODUCTION build is cheaper than the documentation suggests. Among the 12
  jets and their 11 helpers, the debug-assertion AST differs from the proved one **only in
  `f_writeBit`**, whose `simplicity_debug_assert(0 < frame->offset)` guard becomes live
  (test 8).
- That guard holds under `write_frame_at` (`count ≥ 1` and `count <= cursor`), so debug-mode
  coverage needs only a writeBit variant. The rest is AST plumbing.
- Context: `C/Makefile:10` and `C/CMakeLists.txt:30` default to PRODUCTION. The Nix C derivation
  defaults to `production ? false` (`Simplicity.C.nix:5`).

**RC-4 (Low): the per-jet `*_guarantees` are weaker than the value theorems.**

- Where: `jet_guarantees.v:70-81` instantiate `jet_local_spec_guarantees`, which destructs the
  value theorem as `(mf & Hcall & Hobs & _)` (`jet_guarantees.v:38-40`). The per-jet guarantees
  therefore keep only the output cells and the execution guarantees. They drop the final cursor
  (`frame_fields_at`), `write_prefix_at` and the memory framing.
- No per-jet corollary of `jet_context_guarantees` exists.
- Impact is small: `eval_funcall_unique` identifies the two final memories, so the full contract
  can be recovered. It should nonetheless be stated, or `jet_local_spec_guarantees` should keep
  all conjuncts.

**RC-5 (Info): the satisfiability witness is narrow.**

- `jet_layout_witness.v:236-336` exhibits one layout for `increment_64` only. In that layout the
  read frames start at cursor 0, `ctx` has empty `nextData` and no written prefix (`e = 0`), and
  every frame is word-aligned.
- It proves `bm_separated` directly (`witness_separated`, `:208`), not through
  `gap_buffer_layout`, so the evaluator-shaped premise of `gap_buffer_separated`
  (`jet_context.v:193-212`) is never shown satisfiable together with `bm_rep`.
- This is enough to show the context premises are not contradictory. It does not exercise
  crossing words or a nonempty `ctx` prefix or suffix.

### 3.3 Documentation errors

**DE-1 (Medium): `JET_PROOFS.md:257-266` understates the obstacles to using VST.**

- The claim: "an integration is not ruled out. What it would require is a `funspec` treatment of
  the struct-typed parameter …".
- The VST 2.14 manual bundled in the pinned tarball (`doc/VC.tex:240`) lists as unsupported:
  "No `struct`-copying assignments, `struct` parameters, or `struct` returns". Every jet entry
  function has both a struct parameter (`_src : Tstruct _frameItem`) and a struct-copying
  `Sassign (Evar _src) (Etempvar _src)`.
- Verifiable C's `semax` is also a partial-correctness logic. The public theorems assert
  *existence* of a terminating execution plus call-boundary termination facts, which a VST
  proof would not supply without an additional termination or adequacy argument.
- The accurate statement: the entry functions cannot be verified in Verifiable C 2.14 as
  written. Only the pointer-based helpers could be. The direct Clight approach is therefore
  justified on two independent grounds (Section 4.5).
- The claim that `veric/Clight_core.v` uses `function_entry2` is correct (`Clight_core.v:284`).

**DE-2 (Low): `JET_PROOFS.md:297-299` misdescribes the earlier modules.**

- The claim: the earlier position- and crossing-specific modules "are kept as regression tests
  **and as dependencies of the general results**".
- 19 of the 138 jet modules are in no public theorem's dependency closure. They are reachable
  only from `check_jet_assumptions.v`, which is informational and outside `_CoqProject`:
  - `jet_add8_crossing`, `jet_add8_frames`, `jet_add8_input_layout`, `jet_add8_two_words`
  - `jet_increment8_crossing`, `jet_increment8_cursors`, `jet_increment8_frames`,
    `jet_increment8_general`, `jet_increment8_input_layout`, `jet_increment8_position`,
    `jet_increment8_position_call`, `jet_increment8_position_exec`,
    `jet_increment8_position_update`, `jet_increment8_position_word`,
    `jet_increment8_two_words`
  - `jet_one8_call`, `jet_one8_crossing`, `jet_one8_general`, `jet_one8_position`
- They are compiled but not covered by `coqchk` or the gate. That is harmless, because nothing
  public depends on them.

**DE-3 (Low): the static check is weaker than `JET_BUILD.md:59-61` states.**

- The claim: `check-jets.sh` fails when "a jet source contains `Axiom`, `Parameter`, `Admitted`,
  `admit` or `Abort`".
- The grep (`check-jets.sh:33`) matches only at the start of a line, and only in `C/jet_*.v`.
  Test B shows `Lemma … Proof. Admitted.` on one line passing the grep. It also misses
  `Local Axiom` and `#[local] Axiom`.
- The assumption gate compensates for anything a listed theorem uses, so the real guarantee is
  intact. The documentation should say so.

**DE-4 (Low): `JET_PROOFS.md:172-174` and the Coverage table (`:178-185`) overstate
`<jet>_guarantees`.**

- The claim: `<jet>_guarantees` combine the execution guarantees with layers 1 and 3.
- The per-jet definitions combine only with the `jet_local_spec` output cells (RC-4). The
  context combination exists only generically (`jet_context_guarantees`).

**DE-5 (Low): CI caching claims.**

- `ci.yml:40-42` says "the opam switch [is] cached". No step caches the opam switch:
  `opam install -y coq.8.17.1 menhir` runs in both `jets-deps` and `jets` (`ci.yml:53,71`).
  Nothing in the workflow shows that `ocaml/setup-ocaml@v3`'s internal cache includes the Coq
  installation (unverified).
- `JET_BUILD.md:126-132` says the exact-key cache of `Simplicity/`, `jets`, `jet_exec` and
  `jet_write8` covers "the slow serial base".
  - By inspection (not executed): `actions/checkout` gives sources the checkout time as mtime,
    while `actions/cache` restores `.vo` files with their archived, older mtimes.
    `coq_makefile`'s `%.vo: %.v` rule would then rebuild them, making the cache ineffective.
  - This is a performance concern, not a soundness one. A stale `.vo` is also rejected by
    `coqc`'s library digest check and by `coqchk`.

**DE-6 (Info): contradictory wording about Linux regeneration.**

- `JET_PROOFS.md:243-244` says "Linux regeneration is exercised by the `jets-ast` CI job".
- `JET_BUILD.md:134-136` and `:182-184` say the workflow has not been executed. It should read
  "is intended to be exercised".

**DE-7 (Info): the framing clause is broader in prose than in the theorem.**

- `JET_PROOFS.md:40-43` says "every load outside … is unchanged".
- The theorems restrict this to blocks valid in the initial memory (`Mem.valid_block m b`,
  for example `jet_bitmachine_rep.v:160`). That is correct, since the callee's own block is
  fresh and freed, but the prose omits it.

### 3.4 Verification gaps

**VG-1 (Medium): public theorem statements are not pinned.**

- `audit-jet-assumptions.sh` compares axiom *sets*, and `check-jets.sh` checks that the listed
  names exist. Neither records what they state.
- Test A: adding the vacuous premise `(1 = 2)%nat` to `add64_guarantees` kept the axiom set
  unchanged, and the entire gate passed.
- The same weakening could happen to any public theorem during later maintenance, for example a
  premise added to `jet_local_spec` or a conjunct dropped.
- Recommendation: add a statement snapshot to the gate, either
  - `About`/`Check` output for each listed theorem, diffed against a committed
    `jet_statements.expected`; or
  - a Coq file restating each public type, `Check (C.jet_canonical.add64_context : <statement>)`,
    so the statement is maintained as a deliberate specification.

**VG-2 (Medium): the Nix and CI paths are unexecuted, and they differ from the executed
scripts.**

- `coqJets` is not in the CI matrix (`ci.yml:24`), so no automation ever builds it.
- Its `checkPhase` (`Simplicity.Coq.Jets.nix:22-25`) runs `coqchk` but omits:
  - the checks for type-in-type, unsafe fixpoints and assumed positivity (`coqchk` reports
    these but does not fail on them);
  - the library-axiom comparison;
  - the per-theorem gate.
- The Nix CompCert uses `-use-external-Flocq` (`compcert-opensource.nix:68`). The scripts use
  CompCert's bundled Flocq (`LIBRARY_FLOCQ=local`) and VST with `FLOCQ=bundled`
  (`jet-deps.sh:71`), so the two paths check the proofs against different dependency trees.
  The recorded `jet_coqchk_axioms.expected` has been validated only for the script path.
- The full `coq` derivation now also builds all jet modules (`Coq/_CoqProject` +139 lines). It
  stays outside CI because it exceeds six hours.
- All of this is disclosed in `JET_BUILD.md:134-136` and `JET_PROOFS.md:276-277`. The
  weaker Nix check is not.

**VG-3 (Low): AST regeneration was checked on only one host.**

- Byte-equality was reproduced on macOS/arm64 with Apple clang 21 as the preprocessor. Both the
  author's record and my run used this host type. The Linux `jets-ast` job has never run.
- Clang predefined macros or its default `-std` may differ across versions. The
  `-target x86_64-linux-gnu -nostdinc` configuration makes a difference unlikely, but it is
  unverified.

**VG-4 (Info): inherent trust boundaries.**

- `clightgen` (the C-to-Clight step), CompCert's correctness from Clight down to assembly, and
  linking across units are outside Coq. This is disclosed in `JET_BUILD.md:93-101`.
- The regeneration check gives reproducibility of the AST, not correctness of the translation.

**VG-5 (Info): `codespell` was not run on the new files.** The CI `codespell` job scans the
whole repository, including the 29k-line generated `jets.v` and the new Markdown. I did not run
it (see Section 2).

### 3.5 Maintenance recommendations

**MR-1 (Medium): parameterise the width-copied modules.**

- The 16, 32 and 64-bit add, increment and reader files are near-copies with constants
  substituted, for example:
  - `jet_add32_layout.v` and `jet_add64_layout.v`: 155 lines each, 52 differing lines, all
    width constants and names;
  - `jet_read16_layout_total.v` and `jet_read32_layout_total.v`: 101 and 102 lines, 59
    differing;
  - `jet_add32_layout_exec.v` and `jet_add64_layout_exec.v`: 197 and 207 lines, 156 differing.
- The development already has the needed abstraction: `jet_wide.v` defines `wide_size`,
  `wide_reader`, `wide_writer` and `wide_one`, and `one_{16,32,64}` are proved once by
  `eval_one_wide_layout_matches_spec s`.
- Extending that pattern to `wide_add s` and `wide_increment s` would remove roughly 1.5–2k
  duplicated lines. The genuine width differences (the 64-bit wraparound, and the wider carrier
  for 16 and 32 bits) are already isolated in the arithmetic bridges, which can stay
  width-specific.
- There is also a cross-jet coupling: `jet_add32_layout.v:10` imports
  `jet_increment32_layout_exec`.

**MR-2 (Medium): separate the public build from regression artefacts.**

- The 19 modules of DE-2 and `check_jet_assumptions.v` (178 s of `Print Assumptions`, the third
  most expensive file per `JET_BUILD.md:146`) are compiled in every build, including the full
  `coq` derivation, for the 19 modules.
- Either delete the superseded results or move them to a `tests` target outside `_CoqProject`,
  and keep the default target equal to the public closure.

**MR-3 (Low): organise modules the way mainline does.**

- Mainline groups its verified C in `Coq/C/secp256k1/` with a `spec_*.v`/`verif_*.v` split. This
  branch adds 138 flat `Coq/C/jet_*.v` files.
- A `Coq/C/jets/` directory (for example `spec/`, `exec/`, `rep/`, `public/`) would make the
  public surface obvious and match mainline. This is a style point, not a defect.

**MR-4 (Low): the repository now has two ASTs of overlapping code.**

- `Coq/C/jets_secp256k1.v` (mainline, generated by CompCert "22.10-sources" with `-D VST -D
  VERIFY`, no regeneration check) already contains `f_LSBclear`, `f_writeBit`, `f_readBit` and
  others.
- `Coq/C/jets.v` (this branch, CompCert 3.14, PRODUCTION) contains them again with different
  flags.
- Recommendation: one generation pipeline, and the branch's `regenerate-jets.sh` and
  `check-jets-generation.sh` extended to the mainline AST. This branch's AST provenance is
  *stronger* than mainline's.

**MR-5 (Low): the serial critical path is dominated by closed computations.**

- Per `JET_BUILD.md:144-153`, one `cbn; reflexivity` in `jet_write8.v` takes 216 s and one in
  `jet_exec.v` takes 127 s. They sit on the `jets → jet_exec → jet_write8` chain.
- Following the skill's guidance ("extract that constant as its own equality … then rewrite"),
  pre-computing the needed closed facts about the generated helper bodies as small lemmas would
  shorten the serial path far more than `-j`.

**MR-6 (Low): duplicated definitions.**

- `increment8_spec` and `full_increment8_spec` (`jet_spec.v:51-73`) duplicate
  `increment_word_spec 3` (`jet_increment_wide_word.v:8-30`).
- `toZ_injective` is proved three times (`jet_add8_word.v:72`, `jet_add16_wide_word.v:23`,
  `jet_increment_wide_word.v:86`).
- `symbol_read64`, `funct_read64`, `eval_LSBclear8_value` and `write_frame_preserved` are
  defined twice.
- `jet_spec.v` retains early fixed-address lemmas with successful-store premises (for example
  `eval_one8_matches_spec`, `:163-208`), which are unused by public theorems.

**MR-7 (Info): smaller points.**

- `check-jets.sh:52-53` writes the fixed path `${TMPDIR}/jet-coqchk.out`, so concurrent runs
  clobber each other.
- `jet-deps.sh:22` records `VST_COMMIT` but never checks it (the tarball SHA-256 is the real
  pin). GitHub archive tarballs have not always been byte-stable, which could make the pin fail
  closed; Nix's `fetchFromGitHub` NAR hash avoids this.
- The `Set Default Timeout 10` bounds leave about a 4× margin over the author's measured
  maxima. Slower CI runners should be fine, but a failure there would look like a proof
  failure.

---

## 4. Detailed analysis by review area

### 4.1 Implementation and specification (area 1)

**Generation inputs.**

- `jet_translation_unit.c` includes the real `C/frame.c` and `C/jets.c` unchanged.
- `regenerate-jets.sh` runs `clightgen` with:
  - `-std=c11 -normalize -fstruct-passing -DPRODUCTION -IC -IC/include`;
  - a generated configuration (`clightgen-linux.ini.in`: `arch=x86 model=64 abi=standard
    endianness=little system=linux`);
  - clang as preprocessor, with `-target x86_64-linux-gnu -nostdinc`, the CompCert runtime
    headers and the pinned glibc 2.36 headers, plus `-U__GNUC__ -U__SIZEOF_INT128__
    -U__clang__`.
- None of the undefined macros is consulted by `frame.{c,h}`, `jets.{c,h}`, `uword.h` or
  `simplicity_assert.h`. They only select the secp256k1 int128 implementation, which these jets
  do not use.
- `jets.v`'s `Info` block records CompCert 3.14, x86, 64-bit, little-endian.
- The comparison script writes only to a fresh temporary directory and uses `cmp`, which
  detected a one-character change (test C).

**Target typing.** With the pinned headers, `uint_fast16_t`, `uint_fast32_t` and
`uint_fast64_t` are `unsigned long` (`stdint.h:73` under `__WORDSIZE == 64`), and
`uint_fast8_t` is `unsigned char`. So:

- `UWORD` is 64 bits;
- readers 16/32/64 return `tulong`, and `read8` returns `tuchar`;
- `frameItem` is `{UWORD* edge; size_t offset}`, 16 bytes, offsets 0 and 8.

`jets.v` agrees; for example `f_simplicity_add_16` has `fn_temps := (_x, tulong) :: …`.

**PRODUCTION.** In `f_writeBit` the debug guard compiles to `Sifthenelse (Eunop Onotbool
(Econst_int 1)) … Sskip`, which is always false. The proofs execute this guard rather than
assuming it.

**Per-jet check.** The table below was read from the C macros (`C/jets.c:693-764`) and checked
against the ASTs of `add_8`, `add_16`, `one_8` and `increment_64`, and against the carry and
payload models in the bridge modules.

| Jet | Clight function | Carrier and arithmetic | Carry | Payload | Spec (Coq) = canonical Haskell |
| --- | --- | --- | --- | --- | --- |
| `one_N` | `f_simplicity_one_N` | struct copy, then `simplicity_writeN(dst, 1)` | — | constant 1 in N cells | `true >>> left_pad_low word1 wordN` (`jet_spec.v:28-47`, `jet_wide_spec.v:9-12`), which matches `Arith.hs:43` and `Word.hs:129-135` (the `fill` layers pad the high halves with `unit >>> false`) |
| `increment_8` | `…_increment_8` | `read8` gives `tuchar`, promoted to `tuint` | `254 < x` in `tuint`, no wrap | `(tuchar)(x+1)`, mod 256 | `true &&& iden >>> full_increment word8`, with `full_increment = oh &&& (ih &&& (unit >>> zero)) >>> full_add` (`jet_spec.v:51-73`, `Arith.hs:77-88`) |
| `increment_16/32` | `…_increment_16/32` | `tulong`; the constant `1U*UINTn_MAX - 1` is `tuint`, promoted | `2^n - 2 < x`; exact because the reader returns the unsigned value < 2^n | `x + 1` in `tulong`, **not truncated**; `writeN` keeps the low n bits | `increment_word_spec n` (`jet_increment_wide_word.v:8-30`) |
| `increment_64` | `…_increment_64` | `tulong` | `UINT64_MAX - 1 < x` (`increment64_carry`) | `x + 1` **wraps** mod 2^64 | same, n = 6 |
| `add_8` | `…_add_8` | `tuchar` promoted to `tuint` | `255 - y < x` in `tuint`, no wrap | `(tuchar)(x+y)` | `Word.adder 3 = false &&& iden >>> fullAdder` (`Word.v:307-311`), which is `Arith.hs:68` `add` |
| `add_16/32` | `…_add_16/32` | `tulong` | `UINTn_MAX - y < x` in `tulong`; the subtraction would wrap if `y ≥ 2^n`, so reader exactness is necessary and is proved | `x + y` < 2^(n+1), truncated by the writer | `Word.adder 4/5` |
| `add_64` | `…_add_64` | `tulong` | `UINT64_MAX - y < x` (`add64_carry = ltu (sub mone y) x`), the exact overflow test | `x + y` **wraps** | `Word.adder 6` |

- `Word.fullAdder` and `buildFullAdder` (`Word.v:292-305`) are the same combinator tree as
  Haskell `full_add` (`Arith.hs:52-58`), and `Word.zero` is `fill false`.
- The C jet tables associate these functions with matching types, for example
  `[ADD_8] … .jet = simplicity_add_8, .sourceIx = ty_w16, .targetIx = ty_pbw8`
  (`C/bitcoin/primitiveJetNode.inc:26-31`).
- Each public theorem names the concrete `f_simplicity_<jet>` (`jet_canonical.v:76-311`, with
  `wide_one W16 ≡ f_simplicity_one_16` by `exact`), so function selection is checked by the
  kernel.

**Derivation from initial state.** The twelve value theorems quantify over an arbitrary memory
`m`. Their premises are only:

- `frame_base_valid`, alignment, and `frame_fields_at` (or `Mem.loadbytes`, for `one_N`) at `m`;
- input-bit predicates at `m`;
- `write_frame_at m …`, which gives initial *writable permissions* and *initialized* words.

The conclusion is `exists mf, Clight2.eval_funcall ge0 m (Internal f) … E0 mf (Vint Int.one) /\ …`
(for example `jet_add64_layout.v:15-37`). With the axiom sets confined to CompCert's
external-call parameters and standard classical axioms, this establishes that allocation of
`_src`, the `assign_loc_copy`, every helper `Scall`, every store, the return conversion and
`free_list` were constructed inside the proofs.

The internal lemmas with successful-store premises (`JET_PROOFS.md:230-234`) are not public, and
I confirmed they do not appear in public statements.

### 4.2 Representation fidelity (area 2)

`jet_encoding.v` and `jet_bitmachine_rep.v` were checked against `BitMachine.v`, `Translate.v`,
`frame.h` and `eval.c`:

- **Encoding bit order.** `encode (hi, lo) = encode hi ++ encode lo`, and a `Bit` encodes as
  `[Some false]` or `[Some true]` (`Translate.v:46-55`). `encode_word` proves words are MSB
  first, and it is closed under the global context.
- **Read cells.**
  - C: `peekBit` reads word `edge - 1 - offset/64`, bit `63 - offset%64` (`frame.h:55-57`).
  - Coq: `frame_input_bit_at` uses word `edge - 8*(1 + q/64)`, bit `63 - q mod 64`
    (`jet_input_layout.v:30-35`).
  - The read frame's offset is `padding + |prevData|`, with padding `64*ROUND_UWORD(n) - n`
    (`initReadFrame`, `frame.h:31-39`), and cells `rev prevData ++ nextData`
    (`jet_bitmachine_rep.v:70-80`). This un-reverses the zipper correctly.
- **Write cells.**
  - C: `writeBit` decrements `offset`, then writes bit `offset%64` of word `edge + offset/64`
    (`frame.h:80-90`).
  - Coq: the i-th written cell is at `cursor-1-i` (`jet_encoding.v:361-370`).
  - The write frame's C offset is `writeEmpty` (`initWriteFrame`, `frame.h:47-49`). The written
    cells are `rev writeData`, observed from offset `n-1` downwards (`jet_bitmachine_rep.v:82-92`).
  - Moving a write frame into a read frame (`eval.c:335-338`) is consistent with these layouts:
    cell 0 lands at bit `(n-1) mod 64` either way.
- **Padding and `None`.** `cell_matches` requires only that the physical bit exists
  (`jet_encoding.v:94-95`). None of the twelve jet types contains `None` cells; the case matters
  only for context frames.
- **Initialized words.** Every frame word must load as `Vlong`. This is faithful because
  `eval.c:805-807` allocates `cells` with `calloc` "because the frame data must be initialized".
- **Shared blocks.** `bm_layout` has one `cells_blk` and one `frames_blk`, which matches
  `eval.c:807,811`.
  - `bm_rep` requires `cells_blk ≠ frames_blk` and nothing else about distinctness.
  - Disjoint regions within the same block are expressed by offset ranges in `bm_separated`.
- **Unwritten output cells.** These are unconstrained in `write_frame_rep`. The only obligation
  is word initialisation, re-established by `bm_rep_after_write` from the written cells. This
  permits the C writers' `LSBclear` of bits below the final cursor (`frame.c:49-86`), which the
  value theorems' framing clause excludes from preservation.

### 4.3 Context preservation (area 3)

**What the jet modifies**, taken from the generated bodies:

1. the cursor field `[aw+8, aw+16)` of the destination item. The edge field is never written;
2. the cell words from `edge + 8*((cursor-|B|)/64)` to `write_word_address edge cursor + 8`,
   including a crossing lower word;
3. the fresh local `_src` block, which is allocated and freed.

The readers advance `src.offset` **on the local copy only**. The caller's read-frame item is
therefore never written, which matches the Bit Machine: `LocalStateEnd` keeps
`readLocalState = encode a`, so the read cursor does not move.

**Against `bm_separated`** (`jet_bitmachine_rep.v:115-126`):

- (1) is checked against every other item, including the active read item;
- (2) is contained in `[edge_aw, write_region_hi aw)`, and the whole region is required to be
  disjoint from every read frame's word range and every inactive write frame's range;
- (3) is a fresh block. It is excluded by `Mem.valid_block m b` in the framing clause.

The separation is sufficient and slightly conservative: it covers the whole output frame rather
than only the written words, which is harmless because evaluator frames never share a word.

**`bm_rep_after_write`** (`jet_bitmachine_rep.v:350-470`) re-establishes:

- inactive read frames, the active read frame and inactive write frames, via
  `read_frame_preserved` and `write_frame_preserved` under the separation;
- the caller's written prefix `wd`: above the top written word by framing, and within that word
  by `write_prefix_at`, whose `word_outside_eq 0 (1 + (cursor-1) mod 64)` preserves exactly
  bits `≥ cursor`;
- the new written cells from the value theorem;
- the words below, which stay initialized. Unwritten cells are unconstrained.

The context's own empty tail (`e = writeEmpty ctx`) is handled generally.

**`jet_context`** (`jet_context.v:54-123`) instantiates `jet_local_spec` with:

- `bd = bs = frames_blk`, `bi = bw = cells_blk`;
- read cursor `pad + |prevData ctx|`, write cursor `|B| + e`.

It concludes `bm_rep mf L s1 /\ (s0 >>- @t Naive.translate ->> s1)`, the second conjunct being
`Naive.translate_correct Ht a ctx` verbatim. Both conjuncts use the same `s1`, for an
**arbitrary** `ctx`: any prefix and suffix of the active read frame, any written prefix and
empty tail of the active write frame, and any inactive frames. This is the connection the
review asked for.

**All twelve wrappers** (`jet_canonical.v:279-311`) apply `jet_context` with the right function,
the parametricity proof and `*_local_spec`.

**Aliasing.** The value theorems (`jet_local_spec`) allow `bs = bd` and `bi = bw`, including an
output frame that overwrites its own input after reading it. That is correct for the value
statement, since all reads precede all writes in every one of the twelve bodies.
Context preservation needs the stronger `bm_separated`, and the development keeps the two
distinct as required.

**Witnesses.** See RC-5. `gap_buffer_separated` correctly orders items and cells as in
`eval.c:60-90`. The unnecessary restrictions found are RC-1 and RC-2, not the separation
conditions.

**Scope.** Nothing shows that the evaluator establishes or maintains `bm_rep` and
`bm_separated`, and I infer no whole-evaluator result.

### 4.4 Execution and proof integrity (area 4)

- **`step2_determ`** (`jet_clight_determinism.v:135-150`) is proved from the Clight rules and
  CompCert's `external_call_determ`. No determinism axiom is added.
- **`eval_funcall_call_boundary`** (`:347-373`), for every `k` with `is_call_cont k`:
  - there is an `n`-step silent path to `Returnstate res k mf`;
  - every shorter execution is silent, has not returned to `k`, and has exactly one silent
    successor, so it is neither stuck nor branching;
  - every execution of at least `n` steps passes through the return;
  - every infinite execution is the call followed by an infinite execution from the return.
- **Uniqueness** (`eval_funcall_unique`, `:375-396`) covers all terminating big-step results
  with any trace.
- **Divergence** is excluded outright only at `Kstop` (`:398-417`). For a general `k`, the
  results make no claim about the caller after the return, and none assumes the caller
  terminates.
- **Semantics.** The use of `Clight2` (`function_entry2`) is correct for this AST. `_src`
  appears in both `fn_params` and `fn_vars` with an initial `Sassign` from the temporary. That
  is the `SimplLocals` convention, and it would violate `function_entry1`'s `list_norepet`
  check.
- **Assumptions.** The 77 listed theorems use only:
  - `classic`, `functional_extensionality_dep` and the two `ClassicalDedekindReals` axioms;
  - CompCert's `external_functions_sem` and `inline_assembly_sem` (36 value and context
    theorems), plus the corresponding `*_properties` (19 determinism and guarantee theorems).
  
  Ten theorems are closed. `Archi.win64` and the VST, `ProofIrrelevance` and
  `PropExtensionality` axioms appear only as library-level `coqchk` axioms and are not used by
  the theorems. There are no unsafe checker settings.
- **Statements.** The statements match the intended guarantees, apart from VG-1 (not pinned),
  RC-1 (`Vundef`) and RC-4 (the per-jet guarantees drop framing).

### 4.5 Mainline style comparison (area 5)

**Baseline** `91d89ba`. Mainline's verified C is `Coq/C/secp256k1/{spec,verif}_{int128,modinv64}.v`,
together with `extraMath.v`, `progressC.v` and a generated `jets_secp256k1.v`:

- It uses VST Floyd, with `DECLARE … WITH … PRE/POST` funspecs, `semax_body Vprog Gprog f spec`,
  and automation (`forward`, `entailer!`).
- Contracts are separation-logic, `Z`-level functional specifications of internal helpers,
  for example `secp256k1_umul128_spec` in `verif_int128_impl.v:12-24`.
- **No mainline proof verifies a jet entry point with a `frameItem` argument**, even though its
  AST contains them (`f_simplicity_fe_invert` and others).

**The branch** differs in several ways:

- It proves the jet entry points end to end, down to Simplicity terms and the Bit Machine,
  using direct Clight big-step derivations and custom execution tactics (`jet_exec.v`).
- Its contracts are memory-level load and permission predicates with explicit blocks, offsets
  and cursor arithmetic.
- It reuses mainline's `Simplicity.{Alg,Word,Ty,BitMachine,Translate}` specifications well,
  adding no duplicate Simplicity semantics. It does not reuse mainline's C-proof infrastructure,
  which is VST-specific.

**Justified differences:**

- *Direct Clight rather than VST, for the entry functions.* Two independent reasons:
  1. Verifiable C 2.14 excludes struct parameters and struct-copying assignments (`VC.tex:240`),
     and every jet has both. The by-value `frameItem` copy is not an incidental detail: it is
     what keeps the caller's read-frame cursor untouched (Section 4.3).
  2. The public theorems assert existence and termination of the execution, and call-boundary
     determinism. VST's partial-correctness `semax` gives safety only.
- *Explicit block and offset contracts.* The evaluator keeps all frames in two shared blocks, so
  noninterference must be stated with offset ranges inside a block. That is what `bm_separated`
  does.
- *A separate `_CoqProject.jets` and scripts.* The full `coq` derivation exceeds CI's six-hour
  limit, so this is partly justified. The scripts also add AST regeneration, which mainline
  lacks.

**Avoidable differences** (see Section 3.5): width-copied modules (MR-1), dead or legacy
modules and the informational assumption file in the default build (MR-2), the flat layout
(MR-3), two AST pipelines (MR-4), and duplicated definitions (MR-6). None of these justifies
rewriting the proofs in VST. A targeted refactor (MR-1 and MR-2, then MR-3 and MR-4) is
justified by maintenance cost, since every future width or jet would otherwise copy about ten
files.

**What VST reuse or integration would need.** Either:

1. a change to the C jet signature (`frameItem src` to `const frameItem*`), which is an API and
   ABI change for every jet and its users; or
2. an extension of Verifiable C to struct parameters and copies.

In either case it would also need:

- VST funspecs for the pointer-based helpers (`simplicity_readN`, `simplicity_writeN`,
  `writeBit`, `LSBkeep`, `LSBclear`). These are feasible today: mainline's AST already contains
  several of these helpers.
- A representation predicate relating `data_at` of the `cells` and `frames` arrays to `bm_rep`.
- A total-correctness or adequacy bridge from VST's soundness theorem to
  `Clight2.eval_funcall`, which VST 2.14 does not provide.

Without these, a hybrid would lose the existence and termination guarantees.

### 4.6 Reproduction and integration (area 6)

**Build, `coqchk`, gate and AST.** All reproduced from scratch (Section 2, row 4).

- Theorem-list coverage: all 77 entries exist. The list covers every public name in
  `JET_PROOFS.md`'s coverage table and layers.
- The 25 modules checked by `coqchk` are exactly the modules of the list
  (`check-jets.sh:48-52`).
- Failure detection:
  - axioms introduced into a listed theorem: **detected** (test B);
  - a changed AST: **detected** (test C);
  - a changed statement: **not detected** (test A, VG-1);
  - line-internal `Admitted`: **not detected** by the static grep (DE-3).

**Nix and CI, by inspection only:**

- **Target:** Nix CompCert uses `ccomp-platform = "x86_64-linux"` (`default.nix`), consistent
  with the scripts.
- **Pins:** CompCert 3.14 has the same hash in Nix and in the scripts. VST v2.14 is pinned by
  NAR hash in Nix and by tarball SHA-256 in the scripts.
- **Flocq:** external in Nix, bundled in the scripts (VG-2).
- **Missing modules:** `check-jets.sh:36-40` enforces `_CoqProject.jets ⊆ _CoqProject` for jet
  modules. `Simplicity.Coq.Jets.nix`'s source filter includes `C/*.v` and
  `jet_public_theorems.txt`.
- **Stale artefacts:** the `jet-base` cache key covers `jets.v`, `jet_exec.v`, `jet_write8.v`
  (whose only local imports are each other), `Simplicity/**/*.v`, `jet-deps.sh` and
  `_CoqProject.jets`. There is no `restore-keys`.
  - Soundness risk is low: `make` rebuilds dependents, `coqc` rejects inconsistent digests, and
    `coqchk` runs on the final `.vo` files.
  - Effectiveness risk is high, from mtimes (DE-5).
- **Other jobs:** `jets-ast` reuses the `clightgen` binary cached by `jets-deps`, and installs
  clang with `apt-get` but without `apt-get update`. The images ship clang, so this is likely
  harmless.
- **Coverage gaps:** `coqJets` and the full `coq` derivation are not in any CI job.

---

## 5. Claims in `JET_PROOFS.md` and `JET_BUILD.md`, traced

| Claim | Status |
| --- | --- |
| Complete `eval_funcall`, true, empty trace, output = canonical spec (`JET_PROOFS.md:25-37`) | **Verified** from statements (12 theorems), `coqchk` and the gate |
| Final cursor, written prefix, framing (`:38-43`) | **Verified**, with the valid-block qualifier (DE-7) |
| Premises only on initial memory; everything derived (`:45-55`) | **Verified** from statement form and assumptions (Section 4.1) |
| Aliasing permitted; only `bd ≠ bw` required (`:57-62`) | **Verified** (`write_frame_at` in `jet_output_layout.v:9-18`) |
| Encoding equivalences, `encode_word` closed (`:66-84`) | **Verified** |
| `bm_rep` matches `eval.c`; read and write frame layouts (`:89-103`) | **Verified** (Section 4.2) |
| `bm_separated`; `gap_buffer_separated` (`:105-112`) | **Verified**; the witness does not use it (RC-5) |
| `bm_rep_after_write` preserves the caller read frame, inactive frames and prefix (`:114-117`) | **Verified** |
| `jet_context` gives the same state as `translate_correct`; all 12 instantiated (`:123-132`) | **Verified** |
| Witness satisfiability (`:134-140`) | **Verified** for `increment_64` and one layout shape |
| Determinism with no added axiom; call-boundary properties (`:149-174`) | **Verified**; `<jet>_guarantees` wording overstated (DE-4) |
| Assumption lists and counts (`:206-228`) | **Verified** (77, 10 closed, 19 with properties) |
| AST regeneration byte-identical (`:238-244`, `JET_BUILD.md:176-178`) | **Reproduced** on macOS; Linux not executed (DE-6, VG-3) |
| VST integration "not ruled out" (`:257-266`) | **Inaccurate** (DE-1) |
| Earlier modules are dependencies of the general results (`:297-299`) | **Partly false** (DE-2) |
| Static check fails on `Axiom`, `Admitted`, … (`JET_BUILD.md:59-61`) | **Overstated** (DE-3) |
| CI caches opam and the serial base (`JET_BUILD.md:126-132`, `ci.yml:40-42`) | **Not verified; likely inaccurate** (DE-5) |
| Clean build and verification record (`JET_BUILD.md:138-178`) | **Consistent**: 9 min 02 s here for build, `coqchk`, gate and AST at `-j18` |
| Nix and CI not executed (`JET_BUILD.md:134-136`) | **Accurate**; still not executed |

---

## 6. Coverage, uncertainty and limits

**Read in full:**

- `JET_PROOFS.md` and `JET_BUILD.md`;
- all scripts (`jet-deps.sh`, `build-jets.sh`, `check-jets.sh`, `audit-jet-assumptions.sh`,
  `jet-sysroot.sh`, `regenerate-jets.sh`, `check-jets-generation.sh`, `clightgen-linux.ini.in`);
- the CI workflow diff, `Simplicity.Coq.Jets.nix`, the `default.nix` diff,
  `compcert-opensource.nix` and `vst.nix`;
- `jet_bitmachine_rep.v`, `jet_context.v`, `jet_canonical.v`, `jet_guarantees.v`,
  `jet_wide.v` and `jet_wide_spec.v`;
- the statements and structure of `jet_clight_determinism.v`, `jet_encoding.v` and
  `jet_layout_witness.v`, and the specification parts of `jet_spec.v`,
  `jet_increment_wide_word.v`, `jet_add*_wide_word.v` and `jet_increment64_wide_word.v`;
- all 12 value-theorem statements (six printed directly, the rest by diff against those);
- the relevant parts of `BitMachine.v`, `Translate.v`, `Word.v`, `Arith.hs`, `Word.hs`,
  `frame.{c,h}`, `uword.h`, `simplicity_assert.h`, `eval.c` and `jets.c`;
- the generated bodies of `one_8`, `add_8`, `add_16`, `increment_64` and `writeBit`;
- mainline `verif_int128_impl.v` (structure) and `verif_modinv64_impl.v` (structure).

**Not read line by line:** the roughly 15k lines of internal execution, reader and writer proof
scripts. For those I rely on the kernel (`coqc` and `coqchk`) together with my review of the
public statements and the assumption sets. This is appropriate because the checker, not the
reviewer, establishes the proof scripts. What must be reviewed is what the statements claim.

**Uncertain:**

- CI cache behaviour (DE-5), because GitHub Actions was not executed.
- Linux AST regeneration.
- Nix evaluation and build.
- `codespell` on the new files.
- Whether `ocaml/setup-ocaml@v3` caches anything that would shorten the Coq installation.

**Limits of this assessment.** A passing build shows the stated theorems hold for the
generated Clight of one translation unit, under CompCert 3.14's semantics and the listed
axioms. It does **not** show that:

- `clightgen` translated the C correctly (only reproducibility of its output was checked);
- the evaluator establishes the context premises, or that whole programs are correct;
- compiled machine code behaves the same;
- the Nix or CI configurations work.

A negative test shows the gate's blind spot for statement changes (VG-1). Future edits could
therefore weaken the public results without any automated signal until that is fixed.
