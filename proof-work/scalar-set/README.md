# Actual scalar_set_b32 byte parser and owned call

This archive adds four freshly compiled `OriginalC` modules, building on the
unchanged sources in `../scalar-next` and `../scalar-reduce`. Its final result
is `eval_scalar_set_b32_bytes_owned`: the unchanged original Clight function,
with its actual NULL overflow-pointer branch, parses any 32 valid bytes and
stores four limbs whose value is the big-endian input modulo the group order.
The result derives the overflow flag from the real classifier expression;
there is no correct-flag/output/call premise. It also proves actual memory
loads, void return, post-call representation, outside-footprint framing and
retained Freeable permissions on both 32-byte allocated regions.

These are internal reader prerequisites, not public scalar-jet equivalence.
The owned-region contract entails distinct allocated blocks and zero bases.
The reader will establish it using its actual buffer allocation and read8s
call; the public jet must establish its own scalar-local ownership. Nothing
here proves arbitrary public-frame layouts or adds registered jet coverage.

The decomposition is reusable:

1. `jet_secp_scalar_bind` proves expression substitution and the explicit
   signed-32-to-64/back-to-32 identity, without assuming a cast result.
2. `jet_secp_scalar_set_shape` extracts the actual first four C statement
   groups and proves exact correspondence between the complete executor
   output and the verified reduction expressions. It derives the actual
   overflow flag and the reduced output value for arbitrary machine bytes.
3. `jet_secp_scalar_set_bytes` proves the raw 32-byte big-endian value and
   bounds, reusing byte/limb and bitwise-OR lemmas. Its final numeric bridge
   is used by the actual call theorem, not offered as a substitute for it.
4. `jet_secp_scalar_set_owned` reuses actual entry, prefix/suffix composition,
   the proven original-C shift64 oracle and caller ownership. It does not
   replace the C function or assume its execution or local free.

The four final module compilation runs exited 0: bind (immediate), shape
62596, bytes 70079, owned 3000. Earlier owned compilations stopped at an import
or final conjunction mismatch; they are not counted as completed modules.
Per-result Print Assumptions 17783 exited 0: 30 results, 27 closed. Two actual
call results use the same six inherited execution assumptions, and the
load adapter uses the same four inherited classical/extensionality assumptions.
Contract run 60528 exited 0: 30 actual types and 18 non-tree definitions printed
without truncation and reviewed against the sources. The two computed trees
are separately printed by 29777 (exit 0): their run equations, output shapes,
NULL pointer and retained regions are kernel-checkable formal results, while
the deep tree text is diagnostic data, not an omitted-term equality certificate.
Independent kernel run **54545 exited 0**, with 15 imported context axioms and
all three unsafe categories empty. The manifest pins the exact proof sources
and output hashes. The imported-context list is not a per-result assumption set.

Sources and review drivers are archived as `.source`, outside accepted load
paths. Materialized files/logs are in `/tmp/jet-scalar-reverify.8hswEF`. Use the
Coq 8.17.1 toolchain and the normal candidate's Coq directory as in scalar-reduce.
No source or registry in the frozen affine acceptance candidate is changed.
Run `review.py --work /tmp/jet-scalar-reverify.8hswEF` to recheck the pinned
30-result evidence. This is not an acceptance shortcut or public-coverage gate.
The in-memory negative fixtures in `test-review.py` pass: nine source, driver,
contract, tree, dependency and kernel mutations are rejected without changing
any real proof or audit input.

The subsequent `../scalar-reader` milestone now composes actual read8s and
the original NULL scalar_set_b32 call into the original reader body, with
derived loads/value, cursor representation, framing and retained buffer
ownership. Its 31 results are independently kernel checked; this archive's
30-result evidence remains unchanged and still passes its guard.

Next: compose original read_scalar entry and actual allocation around that
body, then prove byte-buffer free, void return and retained caller regions;
then the public scalar_is_zero lifecycle and literal canonical specification
with its source/parametricity gates and full acceptance. SHA and memcpy remain
reserved for the coordinated separate session. All work remains local.
