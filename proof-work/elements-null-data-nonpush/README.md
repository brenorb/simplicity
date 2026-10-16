# Actual non-push tag, padding and payload

Private tree: `/private/tmp/jet-null-data-nonpush.712v8knv`.
Semantic fingerprint:
`f7d32f6477636410a95e23af8cab7911cf48300727e67e0c58a94c081b1b8075`.
The two new sources are archived under `source/`; inherited source bytes equal
the completed `../elements-null-data-payload/` tree. No main/staged semantic
input changed and no live audit objects were copied.

## Formal progress

`C.jet_elements_bit_expr` factors actual calls whose bit/padding arguments are
computed signed-int expressions. Its internal lemmas accept an expression
evaluation derivation and prove the real helper call plus complete frame
effect. Concrete consumers below discharge that evaluation; it is not an
execution or desired output premise of the final arm result. The generic
padding call states the signed-int-to-uint64 conversion bound explicitly.

`C.jet_elements_null_data_nonpush` proves the entire actual non-push arm of
`simplicity_output_null_datum`:

1. Evaluate the actual `2 + 256 - 5` expression and skip253 bits.
2. Reload the opcode through env/transaction/output/opcode memory.
3. Evaluate the actual signed `6 <= code` comparison and write its tag,
   obtaining the returned branch temporary from that real call.
4. Execute the previously checked nibble switch for codes6..21, or the complete
   reserved/negative-one arm for codes4/5.

`exec_elements_null_data_nonpush_arm` proves a258-bit `write_effect` for
`repeat None 253 ++ encode (elements_nonpush_value n bit small)`, where the
value has Simplicity type `Bit + Word4`. Its actual output includes the tag,
all padding and the selected payload; the cursor/prefix/unrelated-memory
effects are retained. It does not assume a tag comparison result or code
temporary binding. Those are derived from the initial opcode loads.

The path relation is preserved across the253-bit padding and then the tag
write, using the whole258-bit separation footprint. Subsequent writable-frame
contracts are derived from earlier effects. Output contents and cursors remain
arbitrary within the shared frame contract. Two closed equalities tie the
condition/choice and padded arm to the actual generated function subtrees.

The opcode interpretation covers all18 non-push kinds: sixteen small integers,
OP_1NEGATE and OP_RESERVED. No whole-jet endpoint or coverage entry is added.
The actual `!1` debug path remains assertion-disabled as in the preceding
reserved-arm proof; no assertion-enabled configuration is established here.

## Verification checkpoint

Fresh checker88739 exited0: both modules explicitly recompiled, all12 results
and11 definitions were reported without elision, Elements AST regeneration
matched and recursive `coqchk` accepted both modules and their dependency chains.
`CHECKED.json` records the terminal commands, logs, tools and source/object hashes.
The full reports identify four closed results, three expression/preservation
results with four inherited assumptions, and five execution results with the
six inherited Coq/CompCert assumptions. No new assumption, admission or
unchecked kernel operation was introduced.

Independent evidence review88018 exited0:38 source/object/assumption/report/log/
kernel-scope corruptions were rejected, including false whole-jet claims.
`EVIDENCE-REVIEW.json` binds the tools, completed independent review and refusal
suite. Recheck with:

```sh
python3 -B proof-work/elements-null-data-nonpush/review.py /private/tmp/jet-null-data-nonpush.712v8knv
```

Development corrections were missing Cop/Bit imports, explicit boolean binder
types, using `Bit.fromBool` (the canonical primitive's `toBit` is local),
qualifying `Datatypes.true/false` after importing Simplicity.Bit, and proving
temporary-name disjointness after substituting the possible identifier. The
latter was inspected in coqtop after two failed automation attempts. These
changed no theorem domain or specification.

## Next obligations

Compose the actual `3 < code` tag call with this non-push arm and the checked
push-data pair arm. That should establish the entire259-bit opcode sum
`(Word2 * Word256) + (Bit + Word4)` for a represented valid opcode, not merely
its separate payload branches. Then discharge the two index reads, output/
opcode bounds and isNullData tests, canonical parsed-script/hash representation,
nullable/empty arrays, wrapper entry/free and complete nested-option encoding.
Do not treat a physical opcode/hash load relation as already established by
the real environment builder.

Actual-main415 and combined418 remain the separate existing acceptance handles
47915/91871. Keep their semantic inputs frozen. This batch adds0 whole-jet
coverage and the every-jet goal remains active/incomplete.
