# Complete original scalar_reduce_512 helper

This is checked internal-helper progress, **not public jet acceptance**.
The eight archived sources prove the unchanged LP64 RECKLESS Clight
`f_secp256k1_scalar_reduce_512` helper computes its original eight-limb
input modulo the canonical group order.

The root `eval_reduce512_numeric_owned_loads` has only the original owned
input/output representation as a premise. It proves actual function entry,
argument binding, all 15 original local allocations, the whole original body,
return and freeing locals, representation after cleanup, current-memory
output loads, the numeric output identity and preservation outside caller
regions. No execution, store, free or output premise is assumed.

## Checked boundary

42 results and 26 definitions in eight modules. 34 results are closed.
Four representation results inherit the existing four classical/extensionality
dependencies; four execution results also inherit CompCert external-function
and inline-assembly semantics (six dependencies total). No new axiom was added.
The independent kernel check reports the inherited 15-axiom library context
with no unsafe type-in-type, fixpoint or positivity categories.

Fresh explicit module build and both complete type/definition and assumption
drivers exited zero. Kernel checking started after those completed and exited
zero. Source, driver, output and kernel hashes are pinned in `manifest.json`
and `REVIEW.json`. Read-only verification:
```sh
python3 proof-work/scalar-reduce512-final/review.py
python3 proof-work/scalar-reduce512-final/test-review.py
```
The reviewer recursively checks earlier prerequisites, including the dependency
fingerprint. Ten in-memory negative fixtures reject nonterminal checks, false
coverage, source/contract/dependency/unsafe-kernel and classification drift.

## Reproduce

Dependency base: `/tmp/jet-scalar-integration.XAMDsw/Coq`.
Scratch load path: `/tmp/jet-scalar-mul.lkomWj`, namespace `MulC`.
Toolchain: Coq 8.17.1, OCaml 4.14.4, CompCert 3.14, VST 2.14.
From the dependency base, with the pinned Coq bin directory first in PATH
and stack limit 65520 KiB:
```sh
perl -e 'alarm 150; exec @ARGV' bash build-jets.sh --coqc \
  -R /tmp/jet-scalar-mul.lkomWj MulC \
  /tmp/jet-scalar-mul.lkomWj/jet_secp_reduce512_function_numeric.v
perl -e 'alarm 300; exec @ARGV' bash build-jets.sh --coqchk -silent -o \
  -R /tmp/jet-scalar-mul.lkomWj MulC MulC.jet_secp_reduce512_function_numeric
```
Rebuild the archived modules in manifest order before consumers after any
source edit; these commands alone do not regenerate prerequisites.

## Scope still open

This helper is not the public scalar multiplication or square jet. Compose the
actual product/reduction caller, then public frame readers, normalization,
writers and cleanup with the **literal canonical Simplicity program**.
Broader evaluator-frame and other jet proofs remain required.

Main registered coverage remains **351/533**, distinct from the separately
accepted scalar-add candidate **359/533** whose main integration is pending.
No registry, production C, canonical specification or remote branch is changed
by this archive. See `CONTINUATION.md`.
