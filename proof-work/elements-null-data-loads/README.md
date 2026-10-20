# Null-data opcode reloads and real selector arms

## Formal progress

`jet_elements_null_data_loads` adds reusable scalar and nested indexed-field
evaluation lemmas. Unlike the older 64-bit-only indexed-field helper, they
handle the opcode pointer and 32-bit enum loads with their actual access modes.
Seven closed layout results compute against the generated composite environment:
output pnd224/isNullData240, parsed opcode pointer0/length8, opcode code32/hash0
and opcode struct size36. Array arithmetic uses the already checked output
struct size248 and explicit non-wrapping offset bounds.

The shared four-set execution proof follows the actual path:
`env->tx -> tx->output -> output[i].pnd.op -> op[j].code`.
It is parameterized by the four temporary names. It derives the resulting
bindings from four ordinary `Mem.load` facts; it does not assume execution or
the desired output. Other temporaries are preserved. A separate lemma proves
the four load facts survive an output `write_effect` separated from their
precise footprint. A general normal-prefix continuation lemma preserves the
right-associated shape of generated Clight statements and composes traces.

`jet_elements_null_data_small` composes that reload with both previously checked
switches. For OP_1..OP_16 and the four push-data kinds, the selector value is now
derived from actual memory, rather than an assumed `_t'31`/`_t'15` binding.
The resulting nibble/two-bit output retains the complete frame effect.
Two closed Coq equalities identify the composed statements as the actual
subtrees of `fn_body f_simplicity_output_null_datum`, not replacement C bodies.

The bounds, current environment/index bindings, actual loaded opcode value and
writable/separated frame conditions remain explicit helper preconditions.
The caller still needs to establish them. **No whole-C jet endpoint or coverage
entry is added.**

## Verification

Fresh checker80195 terminated with exit0: both modules compiled, all19 results
and11 definitions were printed without elision, the generated Elements AST
check passed and both dependency chains passed recursive `coqchk`.
Ten results are closed. Five load/preservation results use the four inherited
classical/extensionality assumptions; four execution/composition results use
the six inherited Coq/CompCert assumptions. The reports name the exact sets.
No new axiom, admission, unchecked cast or skipped kernel check was introduced.

Development corrections were declaration order, an absent constructor-helper
import, explicit index/base arguments before arithmetic, an induction binder
name and the footprint's block type. These were fixed before the successful
fresh check; none changed the theorem domain or C/specification.

## Next obligations

Use the shared reload/continuation and preservation lemmas in the surrounding
branches: derive their path facts from the actual environment representation;
prove index/count/isNullData tests and the second index read; cover all tag
bits and padding, OP_1NEGATE/OP_RESERVED, and the push-data hash payload. Then
compose wrapper entry/free and the exact canonical txNullData/encodeNullDatum
specification. Keep nullable/empty arrays, arbitrary valid frames/cursors,
framing and build configuration explicit. The existing checked helper does
not justify treating the entire parsed-script representation as constructed
by the real caller.

Actual-main415 and combined418 audits remain47915/91871. Keep their semantic
inputs frozen and poll their existing handles. The every-jet goal is active;
this batch adds0 whole-jet coverage and claims no full acceptance.
