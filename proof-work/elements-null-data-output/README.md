# Null-data jet: checked opcode output helpers

## Formal results

`jet_elements_const_bits` proves execution of arbitrary nonempty constant
writeBit sequences terminating in C break, together with the full composed
`write_effect`. The contract retains valid frame/cursor requirements, output
cells, cursor update, prefix preservation, outside loads, permissions and valid
blocks. It does not assume the desired output or execution as a premise.

`jet_elements_null_data_cases` extracts the two actual switch expressions and
case lists from `fn_body f_simplicity_output_null_datum` in `jets_elements`.
Closed equalities identify `_t'31` and `_t'15`, and prove selection of the
actual four-bit and two-bit write sequences. The two execution theorems cover:

- OP_1 through OP_16 (enum6..21), emitting the corresponding Word4 nibble;
- OP_IMMEDIATE/PUSHDATA/PUSHDATA2/PUSHDATA4 (enum0..3), emitting Word2 selector bits.

Both execute in the real `elements_ge`, consume the supplied valid frame and
retain its full framing effect. They reuse the same sequence execution and
effect composition rather than duplicating twenty symbolic-memory proofs.
Their finite closed AST/word equalities use ordinary checked reduction; no
unchecked casts, assumed declarations or admissions are used.

The exact-code range and source/destination temporary bindings are explicit
helper preconditions. They still must be derived from the real caller's loads
and representation. These are **four execution helpers, not jet endpoints**:
two generic writer results and two extracted-switch results. Coverage added0.

## Verification

Fresh checker96346 completed with exit0: both modules compiled, all10 results
and7 definitions were printed without elision, the generated Elements AST
check passed and both complete dependency chains passed recursive `coqchk`.
Six structural/encoding results are closed; all four execution helpers retain
exactly the six inherited Coq/CompCert assumptions. No new assumption was added.

The initial checker also passed compilation/kernel checking, but had copied
progress labels from an older batch. Those labels were corrected and the
complete checker was rerun; the former tools/receipts are retained under
`label-correction/`, not used as current evidence. A no-op negative fixture
(`endpoints=[]`, already the actual scope) was corrected to inject a false jet
endpoint before the successful evidence suite. Neither correction changed a
Coq proof or the specification. An execution-proof edit corrected switch
argument conversion to CompCert's actual unsigned switch semantics.

## Required next work

The whole output_null_datum jet remains unfinished. It still needs both index
reads, count/isNullData checks, parsed-opcode pointer/code loads and their
preservation, OP_1NEGATE/OP_RESERVED padding, push-data hash payloads, all tag
bits/absent branches, wrapper entry/free, and exact environment/specification
composition with the canonical parser and encodeNullDatum. Keep caller/domain
and configuration assumptions explicit. No normal registration, canonical
whole-jet source-admission or full acceptance is claimed here.

Main415 and combined418 audits47915/91871 run independently; keep their semantic
inputs frozen. This is progress toward, not completion of, the every-jet goal.
