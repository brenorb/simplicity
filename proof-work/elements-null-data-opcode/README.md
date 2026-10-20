# Entire actual259-bit null-datum opcode block

## Formal result

`exec_elements_null_data_opcode_block` executes the entire actual opcode block
of `simplicity_output_null_datum`, assuming its two indices have been read and
the selected opcode is represented. It reloads the opcode, evaluates the real
signed `3 < code` comparison, calls `writeBit` to obtain the tag and returned
branch temporary, and executes the previously checked push or non-push arm.
The complete259-bit `write_effect` is exactly the encoding of
`(Word2 * Word256) + (Bit + Word4)`, including the real tag, padding, hash/nibble/
bit payload, cursor, earlier prefix and unrelated-memory effects.

The path relation and hash words are given in the initial memory. Their
preservation across the tag write is derived from separation of the whole259-
bit footprint, and the remaining258-bit writable frame is derived from the
tag effect. The hash-array/separation precondition is conditional on a push
opcode: **non-push cases do not require a readable unused hash payload**.
No execution, expected tag, resulting temporary or desired output is assumed.

A closed equality identifies the complete statement as the actual generated
C subtree beginning with temporary36. It is not a replacement function body.
`elements_opcode_is_nonpush` proves the signed comparison for all valid cases,
not just selected examples.

The constructor adapters cover all22 `txNullDatumF hash256` kinds. The corollary
`exec_elements_null_data_datum` instantiates the C block proof for each kind,
discharging its numeric range. `elements_output_null_datum_present_sem` connects
that same value to the **existing** `Elements.sem Elements.OutputNullDatum`
under successful output lookup, canonical `txNullData` parsing and datum lookup;
push payloads use the existing `mapNullDatum byteStringHash` operation. This
closed bridge does not replace or edit the primitive specification.

This remains an internal block proof, **not whole-C jet equivalence**. The
physical path/address/frame/separation relation still needs to be established
by the caller, and the real environment builder's parsed-script/hash relation
is not discharged. Coq primitive connection is checked here; the independent
Haskell/port source-correspondence gate is not completed by this batch.
No whole-jet endpoint, coverage entry or normal registration is added.

## Verification checkpoint

Development corrections were explicit boolean binder types before a conditional
range, explicit singleton cells/counts for effect composition, and reducing
`fst/snd` before canonical lookup rewrites. The final mismatch was inspected in
coqtop. The primitive's local `encodeNullDatum` is not exported, so the bridge
is proved against its actual exported `Elements.sem`, not an invented exported
name. These corrections changed no theorem domain or specification.

## Continue toward the entire jet

Prove the opcode-count comparison/tag (`j < output[i].pnd.len`) around this
block, including its absent-index padding. Then prove the output-count/
isNullData short-circuit/tag, both actual32-bit reads, canonical parsed-script
environment relation and nullable/empty arrays. Compose wrapper entry/free and
the full261-bit nested-option result, and finish canonical source/admission
review. Existing frame contracts allow arbitrary valid output contents/cursors.
The current assertion-disabled AST/configuration is unchanged; this does not
establish assertion-enabled builds.

Actual-main415 and combined418 remain the existing acceptance handles47915 and
91871 at this checkpoint. Preserve their semantic inputs and do not install418
until both full results actually succeed. This batch adds0 whole-jet coverage;
the every-jet goal stays active and incomplete.
