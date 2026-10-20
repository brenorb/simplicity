# Actual OP_1NEGATE / OP_RESERVED output arm

## Formal result

`exec_elements_null_data_reserved_arm` executes the entire actual inner else
arm of `simplicity_output_null_datum`: the disabled debug loop, `skipBits(dst,3)`,
the four real loads from env through output/opcode arrays, and
`writeBit(dst, OP_RESERVED == code)`. The result is the complete `write_effect`
for `[None; None; None; Some bit]`, with code4 for OP_1NEGATE and code5 for
OP_RESERVED. No execution or desired output fact is assumed.

The opcode memory relation is established in the initial memory and transported
across the padding write using the existing four-region separation/preservation
lemma. The remaining writable frame is derived from the padding effect, not
assumed in the intermediate memory. All cursor positions and initial output
bits permitted by the shared frame contract remain arbitrary.

Four closed source equalities identify the reload tail, padded suffix, debug
loop and complete arm as the actual generated C subtrees. The dead debug body
is extracted from that AST, not replaced with a chosen implementation.
`exec_elements_disabled_debug` is a generic semantic proof that the actual
`!1` conditional skips that body and breaks the loop. This is specifically the
current assertion-disabled configuration; it does not prove an assertion-enabled
configuration. `exec_elements_skip_const` also supplies a reusable constant
padding-call rule with its signed-int-to-uint64 conversion bounds explicit.

The caller must still establish valid path loads, address bounds, environment/
index temporary bindings and separation of the four load regions from the
three-bit padding write. These are physical representation/frame conditions,
not a proof that the real environment builder supplies the canonical parsed
script. This batch adds **zero whole-jet endpoints and zero coverage entries**.

## Checks

Fresh checker82117 exited0: the new module compiled, all10 result types and9
definitions were printed without elision, the Elements AST regeneration check
passed, and recursive `coqchk` accepted the module and dependency chain.
Four source equalities are closed. The six execution results use exactly the
six inherited Coq/CompCert assumptions in the reports; even the call-free debug
loop lemma inherits them through the big-step relation. No new assumed
declaration, admission or unchecked kernel operation was introduced.

Development failures were an uninstantiated expression-list value before its
boolean cast, a closed machine-bound normalization, a missing separation import,
and an explicit frame-length argument before arithmetic. All were fixed before
the fresh check; none changed the theorem's domain or the C/specification.

## Continue toward the whole jet

Combine this arm with the checked OP_1..16 and push selector arms, proving the
remaining tag writes, 253-bit padding, opcode comparisons and push-data hash
payload. Then prove both index reads, output/isNullData/opcode bounds and their
representation, wrapper entry/free and exact canonical `OutputNullDatum`
composition. The canonical encoder maps OP1Negate/OPReserved to the false/true
left alternative respectively; its tag/padding encoding still needs to be
composed with this execution result. Nullable/empty arrays and real caller
construction remain explicit obligations. Do not count these internal arms as
complete jet equivalence.

Actual-main415 and combined418 acceptance audits remain separate live processes
47915/91871 at this checkpoint. Preserve their semantic inputs. The every-jet
goal remains active and incomplete.
