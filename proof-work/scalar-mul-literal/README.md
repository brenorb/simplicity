# Actual scalar multiplication/write chain against the literal result

This milestone closes the arithmetic-to-Simplicity and arithmetic-to-writer
interfaces of the public multiplication proof. Starting with two normalized
scalar stores, the composed root derives the **actual original**
`secp256k1_scalar_mul(a,a,b)` and `write_scalar(dst,a)` calls in sequence and
the exact output
`outs0 ++ encode (canonical_scalar_multiply (a,b))` in the frame invariant.
The canonical term is the existing literal Core program, not a replacement
numeric specification. Numeric identities are internal adapters only.

This is **not the public jet theorem**: the actual two readers, outer
entry/source copy/return/free, evaluator closure and shared-input square case
remain to be composed. It adds **zero** registered jets and changes no C,
specification, registry or accepted snapshot. LP64 RECKLESS remains the build
configuration. `CONTINUATION.md` gives the next public-boundary obligations.

## Checked contracts

- `four_words_scalar_limbs`: any four actual uint64 words are exactly the
  limbs recovered from their weighted value. It reuses the checked radix
  lemma and `Int64.repr_unsigned`; no exhaustive enumeration is needed.
- `scalar_writer_initial_rep_from_mul`: derives writer representation from
  the multiplication's actual post-free loads and output ownership. Exact
  `Vlong` loads, not only their decoded value, are retained.
- `scalar_mul_initial_rep_from_storage`: derives the two-region helper
  representation from actual scalar storage and Freeable permissions, with
  an explicit disjoint-operand condition. `scalar_mul_normalized_input_values`
  supplies both numeric equalities for that constructed rho.
- `eval_scalar_mul_literal_owned`: complete original scalar multiplication
  call producing writer-ready representation of the literal canonical result.
  Its normalization equalities are intermediate reader-bridge premises, not
  premises intended for the final public theorem.
- `eval_scalar_mul_write_literal`: complete multiplication then complete
  writer execution. The writer's input representation and post-multiplication
  invariant are **derived** in the same current memory. Its preconditions are
  input representation/normalized values, external-block separation, the
  existing output-frame invariant and 256 bits of remaining capacity; neither
  a helper execution nor output nor post-memory invariant is assumed.
- `eval_scalar_mul_write_from_normalized_storage`: same sequence starting
  from the two normalized scalar stores, discharging the symbolic helper
  representation and numeric equalities internally. It retains arbitrary
  valid output cursor/layout, existing output prefix, exact literal encoding,
  surviving destination ownership and outside-operands/external framing.

`jet_secp_scalar_writer_word.v` is reused **byte-for-byte** from the pending
scalar-add candidate. Its generic Word256 writer contract already existed;
this archive does not count it as a newly proved jet. The source path/hash is
pinned in the manifest. Promotion should share one `C` module, not register
two competing copies.

The composed postcondition does not yet expose the **second operand's**
Freeable permission after multiplication. That is a necessary interface
extension for the public wrapper's cleanup, not a C correctness finding.
The frame outside both operands cannot establish that permission by itself.

## Evidence and limits

`REVIEW.json` records terminal fresh build and independent kernel results,
source/compiled-object/report hashes, toolchain and verification scope. All
six modules and both drivers were rebuilt in order with proof sources frozen.
The full report contains 17 result types and two definitions (31,494 bytes).
Seven results are closed; four representation results retain four inherited
classical/extensionality dependencies; two numeric bridges retain inherited
functional extensionality; four execution results retain the inherited six
dependencies including CompCert's semantic parameters. No new axiom or skipped
proof is introduced. The expected dependency-wide kernel context is the
existing 15-axiom context, with all three unsafe categories empty.

Production/canonical source identity passed for 240 files; the immutable Coq
dependency fingerprint is unchanged. Full AST regeneration and integrated
acceptance were **not** run. Sources and drivers are durable here; the frozen
compiled artifacts and logs remain in the local scratch directory.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 proof-work/scalar-mul-literal/review.py
PYTHONDONTWRITEBYTECODE=1 python3 proof-work/scalar-mul-literal/test-review.py
```

The reviewer also validates the earlier function/body/helper receipts and
exact reuse of the generic writer. Sixteen corruption fixtures operate only
in memory; they do not edit proofs or acceptance snapshots.

Use the toolchain/build setup in `../scalar-mul-function/README.md`, additionally
mapping `/tmp/jet-scalar-mul-public.nzHcef` to `PubC`. Rebuild all six manifest
modules in order, then `public_assumptions.v` and `public_contracts.v`, using
`build-jets.sh --coqc`. Compiler processes were bounded at 150 seconds each.
The kernel root is `PubC.jet_secp_scalar_mul_write_chain`, using
`build-jets.sh --coqchk -silent -o` with the `MulC`, `LifeC` and `PubC` mappings
and a 600-second process bound. The first 300-second kernel attempt reached
its deadline (exit 142) with no proof diagnostic; at 4:38 wall time the scoped
process check showed 2:05 CPU time and 2,757,456 KiB RSS. Its empty log is
preserved separately. The unchanged closure was then retried with the longer
bound; only its successful terminal result qualifies as verification.
Coq 8.17.1 / OCaml 4.14.4, CompCert 3.14,
VST 2.14; stack 65,520 KiB. Rebuilds require new receipts; old `.vo` files do
not verify edited sources. Preserve old frozen evidence and unrelated dirty
work. Signed atomic local commits only; never push.
