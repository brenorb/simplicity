# Elements tap_env_hash: literal program composition and original C getter

Private tree: `/private/tmp/jet-elements-tapenv.blTXWMDA`.
Seed: completed seven-stream-getter Elements proof tree
`/private/tmp/jet-elements-stream.1zVQb2CU`. The compiled tapleaf dependency
was copied as source only and recompiled here. No object from a running kernel
or full-audit tree was copied; main Coq inputs/stage stay unchanged.

`C.jet_elements_tap_env_hash_program` defines the original program composition:
initialize SHA, absorb the tapleaf hash, then the tappath hash and `InternalKey`,
and finalize. It reuses the checked generic Reader and SHA results, the literal
Elements tapleaf semantics, and the checked 8-bit tappath program semantics.
The final theorem covers actual `f_simplicity_tap_env_hash` execution in
`elements_ge`, with the computed value in the explicit taproot cache/frame
relation at offset72. It does not assume the desired C execution/output.

The complete fresh dependency/module compilation and type/assumption reporting
phase passed:

```sh
python3 -B proof-work/elements-tapenv/check.py compile /private/tmp/jet-elements-tapenv.blTXWMDA
```

`RUN.json` and exact logs record all three new results and two definitions.
The parametric result is closed, the pure semantic result uses inherited
functional extensionality, and the C endpoint has exactly the six inherited
assumptions. The 96-byte SHA length bound is discharged. No new axiom,
desired-execution premise or kernel bypass is introduced.

Canonical-source review and38 read-only corruption fixtures passed, recorded
in `../elements-tapenv-source/`. The once-only recursive-kernel/AST phase
completed with exit zero under handle49735:

```sh
python3 -B proof-work/elements-tapenv/check.py kernel /private/tmp/jet-elements-tapenv.blTXWMDA
```

`CHECKED.json`, `KERNEL-RUN.json`, `ast.log` and `kernel.log` bind the actual
recursive kernel and Elements AST-regeneration success. Independent evidence
review also completed with exit zero, including55 proof/kernel/command/source/
report/object/dependency corruption fixtures. `EVIDENCE-REVIEW.json` and
`evidence-tests.log` bind that separate stage and the completed tapleaf
dependency review. Its historical source map is checked against actual
immutable private-tree bytes, not a requirement that main stay420 forever.
Normal registration/admission remains. This is not accepted extra coverage or
full normal acceptance. The separate private443 full audit and main420
source/index checkpoint remain frozen.

The native Haskell `Schnorr.PubKey` wraps `Word256`; `encodeKey` uses its integer
conversion. This getter/program does not deserialize arbitrary bits as a field
element or prove curve validity. Host-library correspondence and actual caller
cache establishment remain separate obligations; source review must preserve
this native-word boundary.
