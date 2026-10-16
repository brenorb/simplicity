# Complete output_null_datum C call against the primitive

Private tree: `/private/tmp/jet-null-data-wrapper.wudp6ve6`.
Fingerprint:
`0f004fc67ff120fd27fe850bd1f6e0e3cb9e3d315c4dbdcd0094ded7cf314f49`.
The new source is archived under `source/`; inherited sources equal the checked
`../elements-null-data-rest/` tree byte for byte. Main418 semantic inputs and
the original staged patch remain unchanged.

## Completed implementation-to-specification statement

`elements_output_null_datum_initial_equivalence` proves the actual
`Clight2.eval_funcall elements_ge m (Internal f_simplicity_output_null_datum)`
against `Primitive.Combinators.prim Elements.OutputNullDatum`, with the result
encoded by Simplicity's canonical `encode`. It includes function entry, actual
16-byte local allocation, by-value frame copy, both readers, every output
alternative, return conversion and actual local free. Public framing no longer
excludes the private block; it preserves every old valid load outside the
destination cursor and output word ranges, as well as the earlier output
prefix. No execution, desired output or missing lifecycle step is assumed.

The new initial selected-opcode predicate does not mention the not-yet-allocated
private block. Its freshness is derived from `Mem.alloc` and an old opcode-code
load. The frame copy is obtained from the real source bytes; local cursor
writability follows from allocation and storebytes. Generic successful-load
transport lemmas move only initial representations into the actual copy memory.
The existing `elements_wrapper_layout` discharges the full wrapper lifecycle.

The internal `eval_elements_null_data_output_block` uses a valid output block.
`eval_elements_null_data_nullable_layout` removes that premise: an in-range
output's flag load establishes validity, while an out-of-range index never
needs its output pointer. For the latter case the proof reuses the old valid
transaction block as an unused mathematical witness, without changing any
stored pointer or executing any extra read. The final equivalence requires no
output-block validity premise, opcode pointer or second input word when the
outer guard fails.

## Explicit premises and limits

This is one complete C-function equivalence **under the stated initial physical
and separated-layout premises**, not normal acceptance of another jet yet:

- The source frame is aligned, non-wrapping and represents the first Word32.
  Its cursor has room for64 input bits.
- The initial C environment has the output-count/null-data representation.
- If the outer guard succeeds, the remaining Word32 is represented; its words
  and all later-read environment/hash ranges avoid the complete261-bit output
  footprint and destination cursor. Read/write data may share an allocation;
  arbitrary valid cursors and word-boundary crossings remain supported.
- The represented opcode count, code and (for pushes) cached hash words agree
  with the parsed logical script. The logical output/script lookup is tied to
  the actual count/flag guard. This is an environment correspondence premise,
  not a proof that the real Elements environment builder establishes it.

The last two bullets must be packaged and instantiated by a public, reviewed
environment/frame contract. Existing `application_jet_local_spec_sep` only
separates environment ranges from output; it does not separate unread input
from output. Do not claim this theorem proves that broader contract, hide input
separation inside an environment predicate, or silently narrow the all-jet goal.
`C.jet_read_after_write.bm_active_read_word_out_sep` provides the actual shared-
allocation derivation for evaluator-valid Bit Machine states; the next adapter
should use it explicitly. The native overlapping-frame API discrepancy remains
open (`../null-data-overlap-probe/README.md`). No unrestricted overlapping-buffer
equivalence or production-evaluator counterexample is asserted.

The target remains the pinned assertion-disabled Elements program. Canonical
Haskell/Coq-port source fidelity review, a public contract adapter and normal
admission remain. Nothing here changes C, a header, a canonical specification
or a main acceptance snapshot. Registered coverage remains418/533, not419.
No clean-HEAD reproduction is claimed for the dirty main tree.

## Verification

The complete module compiled with pinned Coq8.17.1 / CompCert3.14. Fresh
checker39989 exited0 after explicitly recompiling it, printing all8 result types
and3 definitions without elision, regenerating the Elements AST and recursively
kernel-checking the dependency chain. Independent evidence review27671 exited0
with35 deliberate proof/evidence corruptions rejected. A separate terminal
postcheck revalidates the receipt/log/tool hashes, fresh source/object identities
and unchanged main inputs before commit.

Expected assumptions: one closed wrapper-shape result, four shared representation
results using the four inherited classical/extensionality assumptions, and three
complete-call results using the six inherited Coq/CompCert assumptions. No new
axiom, admission or unchecked kernel operation is introduced. The receipt's
`whole_c_endpoints=1` describes the explicit-layout endpoint above;
`normal_registration=false`, `coverage_added=0` and `full_acceptance=false` remain
mandatory until the outstanding contract/source/admission work is done.

```sh
python3 -B proof-work/elements-null-data-layout/review.py /private/tmp/jet-null-data-wrapper.wudp6ve6
```

Development corrections: derive source-block validity from its actual edge load
before allocation/loadbytes transport; retain the count-test expression when
specializing the nullable case without rewriting the boolean equality's other
side; import the existing option instance and specify the full semantic value
instead of an ambiguous placeholder. Checker15350 stopped before writing a
launch receipt because a copied execution-name inventory still named the old
rest theorem. Corrected checker39989 validates the declaration inventory before
compilation and starts a new fresh run; the proof source did not change for that
tooling correction.

## Next steps

1. Build an explicit evaluator-valid contract from `bm_rep`/`bm_separated` and
   canonical input cells; derive unread-j separation with the existing range
   lemma, not an extra opaque precondition.
2. Give the environment relation a concrete footprint and relate its logical
   output/script lookup to the C count/flag/opcode/hash loads. Keep empty outputs,
   non-null-data scripts, absent indices and all22 datum constructors.
3. Review canonical Haskell/Coq-port fidelity and the exact final endpoint type,
   definitions and assumptions, then run the normal admission pipeline. Do not
   count this isolated endpoint as installed/accepted coverage beforehand.
4. Separately validate/resolve the broader API's overlap domain; do not alter C
   or its public interface merely to make an existing contract fit this result.
