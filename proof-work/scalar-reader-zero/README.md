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

Compiler bridge session 71163 and the parametricity compile exited 0.
Assumptions session 37406 and the untruncated six-type/one-definition contract
driver exited 0. Independent kernel session 7411 exited 0: 15 inherited context
axioms, all three unsafe categories empty. Four results are closed; the
ownership adapter uses four inherited classical/extensionality assumptions;
the helper execution result additionally uses CompCert's two execution
semantics parameters. Each result's exact set is checked by `review.py`.

The fresh literal-source gate checks the current Haskell dispatch/types,
group constant and both term structures against the actual compiled ports.
It also invokes the existing recursive subtraction/is_zero/equality dependency
gate on the accepted dependency candidate. Eleven in-memory negative fixtures
reject constant, width, branch and recursive-combinator mutations. Source gates
are correspondence checks, not a replacement for Coq execution or parametricity.
`LITERAL-REVIEW.json` records the exact top-level source hashes used.

```sh
python3 proof-work/scalar-reader-zero/review.py --work /tmp/jet-scalar-reverify.8hswEF
python3 proof-work/scalar-reader-zero/test-review.py /tmp/jet-scalar-reverify.8hswEF
python3 proof-work/scalar-reader-zero/check-literal.py --repo /Users/brenorb/code/PROJECTS/BLOCKSTREAM/simplicity --source /tmp/jet-scalar-reverify.8hswEF --coq /tmp/jet-ge-negate-accept.5mtyZa/Coq
python3 proof-work/scalar-reader-zero/test-literal.py /Users/brenorb/code/PROJECTS/BLOCKSTREAM/simplicity /tmp/jet-scalar-reverify.8hswEF /tmp/jet-ge-negate-accept.5mtyZa/Coq
```

Sources are `.source` archives outside accepted load paths. Reproduce compilation
and coqchk with Coq 8.17.1, stack 65520 KiB, cwd the dependency candidate's Coq
directory, and narrow `-R /tmp/jet-scalar-reverify.8hswEF OriginalC`. The exact
kernel command is in the manifest. Reader function lifecycle is already checked
in `../scalar-reader-lifecycle`; these results consume its actual final region.

Public scalar-zero entry/source-copy/read/helper/writeBit/true-return/local-free
composition and normal full acceptance remain open. Public coverage added: zero;
registered checkout still 351/533. No caller execution, output or free is
assumed in a public equivalence claim. Claude retains memcpy/SHA scope.
