# Actual push-data selector and hash payload

Private tree: `/private/tmp/jet-null-data-payload.ln1s88vi`.
Semantic fingerprint:
`49daa6c61eee71a987f4e559fd8d28cf4de861f63d6b9019d9dc8877422135c2`.
The new `C.jet_elements_null_data_payload` source is archived under `source/`.
Every inherited source equals the completed `../elements-null-data-reserved/`
tree. No main/staged semantic input changed; no live audit objects were copied.

## Formal progress

`exec_elements_null_data_push_arm` executes the entire push-data arm of
`simplicity_output_null_datum`: reload the code through the four actual loads,
execute the two-bit switch for OP_IMMEDIATE/OP_PUSHDATA/OP_PUSHDATA2/OP_PUSHDATA4,
reload the three real pointers, and call the internal `writeHash` on
`output[i].pnd.op[j].dataHash`. It proves the full 258-bit `write_effect`, including
cursor, prefix, other loads, permissions and valid blocks.

The hash array and all four path loads are given in the **initial** memory.
Their preservation after the two selector writes is proved using separation
from the whole 258-bit output footprint. The remaining 256-bit writable frame
is derived from the selector effect. No execution, desired output or
intermediate-memory representation is assumed.

`exec_elements_null_data_push_pair` specializes the eight stored words to a
`hash256` and reuses the checked digest/word bridge: these actual output cells
are exactly the Simplicity `Word2 * Word256` pair encoding. This is an
implementation-to-encoding result for a real C arm, not just a pure
specification identity. Two closed equalities tie the hash tail and entire
selector-plus-payload arm to the actual generated function subtrees.

The shared three-load helper is parameterized by temporary names, so later
parsed-output consumers can reuse it. Pointer arithmetic uses the actual
36-byte opcode size and zero dataHash offset, not guessed layouts.

Physical load/address/frame/separation premises remain explicit. In particular,
this batch does not derive the stored `dataHash` from hashing raw push bytes.
The canonical `txNullData`/`mapNullDatum byteStringHash` caller relation still
needs to establish that connection. **Zero whole-jet endpoints or coverage
entries are added.**

## Verification

Fresh checker82468 exited0: the new module compiled, all8 results and7 definitions
were reported without elision, the Elements AST regeneration check passed, and
recursive `coqchk` accepted the module and dependencies. Three results are
closed; five execution results use exactly the six inherited Coq/CompCert
assumptions named in the reports. No new assumed declaration, admission or
unchecked kernel operation was introduced.

Independent evidence review82823 exited0 and is recorded in
`EVIDENCE-REVIEW.json`. It rechecks source/object/report/command/log identities
and rejects35 corruptions, including changed assumptions, kernel scope and
false whole-jet claims.
`CHECKED.json` binds the fresh compilation and kernel evidence. Recheck with:

```sh
python3 -B proof-work/elements-null-data-payload/review.py /private/tmp/jet-null-data-payload.ln1s88vi
```

Two development corrections were using the existing `encode_length` lemma
(instead of an unavailable name) and specifying the preservation lemma's cursor
before arithmetic. Neither changed any theorem domain or implementation.

## Next composition

The actual inner push arm, small-integer switch and reserved/negative-one arm
are now separate checked pieces. Next derive the signed opcode comparisons
and their returned tag bits from the loaded code, compose the non-push branch
with its 253-bit padding and five-bit alternative, and then compose the outer
259-bit opcode sum. Keep expression trees exact: the actual padding count is
`2 + 256 - 5`, not an `Econst_int 253` in the AST.

Then discharge both index reads, bounds and isNullData tests, nullable/empty
arrays, canonical parsed-script/environment representation, wrapper entry/free
and the complete nested-option encoding. The assertion-disabled configuration
of the existing AST is unchanged; assertion-enabled behavior is not established.
Actual-main415 and combined418 audit inputs stay frozen while handles47915 and
91871 are live. The every-jet goal is active and incomplete.
