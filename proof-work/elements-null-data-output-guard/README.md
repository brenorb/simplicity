# Actual outer output-count/isNullData short circuit

Private tree: `/private/tmp/jet-null-data-output-guard.gnzvh6__`.
Semantic fingerprint:
`91b1eff79486be9c792a742ab34a241319e5f7a83f04057d122ba13a7d47c501`.
The new `C.jet_elements_null_data_output_guard` source is archived under
`source/`. All inherited source bytes equal the completed
`../elements-null-data-index/` tree. No main/staged semantic input changed;
no live audit objects were copied.

## Formal result

`exec_elements_null_data_output_guard` executes the actual outer condition
of `simplicity_output_null_datum`: load the transaction and numOutputs, evaluate
the unsigned `i < numOutputs`, load output[i].isNullData only on that true
branch, execute its actual boolean cast, then call `writeBit` with the resulting
tag. The returned temporary and full one-bit `write_effect` are proved, not
assumed. The prefix's exact temporary bindings and preservation of every other
temporary are also exposed for the remaining function composition.

The representation requires only env/transaction/count loads unconditionally.
The output pointer, indexed address bounds and Mint8unsigned boolean load are
conditional on an in-range index. `elements_null_data_output_rep_out_of_range`
constructs it without any readable output-array pointer, even if the count is
zero. This is the actual short-circuit behavior, not an unconditional array
assumption. The logical isNullData bit remains an explicit physical field
relation, to be connected to the real parser/caller later.

The count offset704, output pointer offset8, output size248 and boolean offset240
are inherited checked composite-layout facts. The final closed source equality
identifies the entire guard as the actual generated C subtree. No replacement
function body, branch result, desired execution or output fact is assumed.
Writable output contents/cursors remain arbitrary within the shared contract.

This is not yet the complete output_null_datum function: the second input read,
true-path opcode-index block, false-path260-bit padding and wrapper/free still
need composition. No whole-jet endpoint, normal registration, canonical source
gate or coverage entry is added.

## Verification checkpoint

Fresh checker1558 exited0: the new module explicitly recompiled, all8 results
and7 definitions were reported without elision, Elements AST regeneration
matched and recursive `coqchk` accepted the module and its dependency chain.
`CHECKED.json` binds source/object, tools and terminal command/log hashes.
Reports identify five closed results, one
representation result with four inherited assumptions and two execution
results with the six inherited Coq/CompCert assumptions. No new assumption,
admission or unchecked kernel operation was introduced.

Independent evidence review22017 exited0:35 source/object/assumption/report/log/
kernel-scope corruptions were rejected, including false whole-jet claims.
`EVIDENCE-REVIEW.json` binds the tools, successful independent review and refusal
suite. Recheck:

```sh
python3 -B proof-work/elements-null-data-output-guard/review.py /private/tmp/jet-null-data-output-guard.gnzvh6__
```

The main prefix/guard execution compiled directly. The out-of-range constructor
was repaired after inspecting coqtop: unrestricted `repeat split` had introduced
the condition and split its consequence, so the proof now splits the six
unconditional fields explicitly before deriving the contradiction. No theorem
domain or implementation changed.

## Continue

Compose the guard with the actual second read32 (only when this guard returns
true), then the checked260-bit opcode-index block, or the actual false-path
padding expression `1 + 1 + 2 + 256`. Preserve source-frame-local mutations and
the initial environment relations across all output writes. Add the first
read32, function entry/free and the complete261-bit primitive result. Establish
the isNullData/list/hash relation from the real parsed-script caller, including
empty/nullable arrays. The existing assertion-disabled AST is unchanged;
assertion-enabled builds and canonical Haskell/port source/admission review
remain separate obligations.

Important read-after-write boundary: the first output tag is written **before**
the second input word is read. The single-read `elements_read_wide_step` cannot
simply be reused as if that input were unchanged: it combines allocation/copy
with the first read. Prove a current-local-frame reader step from the existing
`eval_read_wide_word_at` plus Elements transport, and derive preservation of
the unread word across the guard write from valid Bit Machine frame separation.
The older `application_jet_local_spec_sep` interface has no general input/output
separation premise and alone cannot justify this carry-over for arbitrary
overlapping buffers. Do not add preservation as an assumed execution/output
fact or claim correctness on unsupported overlapping layouts. Choose the frame
predicate from the actual caller's validity guarantees and prove its adequacy;
if valid layouts share a machine word, use bit-level preservation rather than
silently requiring disjoint blocks. This is a proof-contract boundary, not a
confirmed implementation/specification mismatch.

Actual-main415 acceptance47915 completed successfully and is independently
archived in `../elements-issuance-amount-admission/`. Isolated combined418
remains91871 at this checkpoint; preserve its semantic inputs and do not
install until its full result succeeds. This batch adds0 whole-jet coverage;
the every-jet goal stays active and incomplete.
