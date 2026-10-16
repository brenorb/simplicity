# Actual opcode-index check: present, absent and empty

Private tree: `/private/tmp/jet-null-data-index.qh4eih59`.
Semantic fingerprint:
`050021c2298928580c5ca57fc30f79729d4b6dd4fe36965a72c608dddb3f08fc`.
The new `C.jet_elements_null_data_index` source is archived under `source/`.
All inherited source bytes equal the completed `../elements-null-data-opcode/`
tree. No main/staged semantic input changed; no live audit objects were copied.

## Formal result

`exec_elements_null_data_index_block` executes the actual260-bit sub-block of
`simplicity_output_null_datum` after both indices have been read:

1. Load env->tx, tx->output and output[i].pnd.len at their actual layouts.
2. Evaluate the real unsigned-long `j < len`, write its tag and obtain the
   returned branch temporary from that actual call.
3. When present, execute the checked259-bit opcode block; otherwise evaluate
   the actual `1 + 2 + 256` expression and skip259 cells.

The complete `write_effect` is exactly the encoding of the Simplicity optional
opcode result (`Unit + ((Word2 * Word256) + (Bit + Word4))`). It retains cursor,
earlier prefix, unrelated loads, permissions and valid blocks. Initial output
contents and cursors remain arbitrary within the shared frame contract.

`int64_index_below_list_length` derives the actual machine comparison from
list lookup, under an explicit64-bit length representability bound. The stored
count equals that represented list length; a comparison/branch result is not
assumed. The selected opcode/hash relation is given only in the **initial**
memory and transported across the tag write, deriving the remaining frame and
all subsequent load facts.

Crucially, `elements_null_data_index_selected` is conditional on a successful
lookup. `elements_null_data_missing_selected` proves it without any opcode
pointer, opcode-array readability or hash payload when the lookup is absent.
This includes an empty parsed script with a null opcode pointer. The count
path itself needs only the transaction/output/length loads, not an opcode
pointer. The absent branch therefore does not reproduce the earlier nullable-
array representation mistake.

A closed equality identifies the complete block as the actual generated
subtree beginning with temporary40. `elements_output_null_datum_parsed_sem`
connects its present **and absent** result to the existing Coq
`Elements.OutputNullDatum` semantics for a successfully located output and
parsed script, with the physical/logical second-index equality explicit.
No primitive definition is changed or replaced.

The caller still has to establish the count/selected physical relation from
the real parsed-script environment, both input reads, the output-count/
isNullData test, and wrapper entry/free. The existing64-bit length bound is
explicit, not proved constructible here. This is not a whole-function endpoint,
normal registration, Haskell/port source gate or coverage addition.

## Verification checkpoint

Fresh checker7801 exited0: the new module explicitly recompiled, all8 result
types and10 definitions were reported without elision, Elements AST regeneration
matched and recursive `coqchk` accepted the module and its dependency chain.
`CHECKED.json` binds source/object, tools and terminal command/log hashes.
Reports identify three closed results, three
expression/representation results with four inherited assumptions and two
execution results with the six inherited Coq/CompCert assumptions. The
missing-selection lemma inherits four through the proposition it states; it
is not claimed closed. No new assumption, admission or unchecked kernel
operation was introduced.

Independent evidence review6133 exited0:35 source/object/assumption/report/log/
kernel-scope corruptions were rejected, including false whole-jet claims.
`EVIDENCE-REVIEW.json` binds the tools, successful independent review and refusal
suite. Recheck:

```sh
python3 -B proof-work/elements-null-data-index/review.py /private/tmp/jet-null-data-index.qh4eih59
```

Development compiled directly without proof repair. The assumption review
corrected the expected closedness of the missing-selection lemma to match
`Print Assumptions`; no theorem was weakened or changed to do so.

## Continue

Prove the actual outer output-count/isNullData short circuit and its tag and
absent-output padding, integrating the second32-bit read only on that true
path. Compose both source-frame reads, canonical raw-script/environment
representation, wrapper entry/free and the complete261-bit result. Maintain
the absent/empty conditional pointer discipline, arbitrary valid frame layout
and exact AST expressions. Assertion-enabled builds and independent canonical
source/admission review remain outside this internal-block checkpoint.

Actual-main415 acceptance47915 has completed successfully and is independently
archived in `../elements-issuance-amount-admission/`. Isolated combined418
remains91871; do not install it until that full audit succeeds. The every-jet
goal remains active and incomplete; this batch adds0 whole-jet coverage.
