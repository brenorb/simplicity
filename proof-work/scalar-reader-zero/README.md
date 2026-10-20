# Original reader output to original scalar-zero helper

Six compiled and independently kernel-checked results adapt actual reduced
reader limbs to the unchanged `f_secp256k1_scalar_is_zero` helper. The ownership
adapter derives its four-limb region from actual reader loads and retained
Freeable storage. It does not assume a canonical machine scalar or the desired
helper return. `eval_scalar_zero_after_reader` proves actual helper execution
and its literal canonical scalar-zero result for arbitrary Word256 input.
The numeric value premise of the previous helper theorem is now discharged
from the reader reduction theorem and canonical input-bit decoding.

The canonical term tests **raw zero OR raw group order**. This is essential:
the C reader reduces modulo the group order before testing zero. No premise
excludes the group-order input. Numeric lemmas are internal bridges; the
result names the literal Simplicity term. The two new parametricity lemmas
prove both scalar terms are core-algebra terms, not arbitrary functions.

Public scalar-zero entry/source-copy/read/helper/writeBit/true-return/local-free
composition and normal full acceptance remain open. Public coverage added: zero;
registered checkout still 351/533. No caller execution, output or free is
assumed in a public equivalence claim. Claude retains memcpy/SHA scope.
