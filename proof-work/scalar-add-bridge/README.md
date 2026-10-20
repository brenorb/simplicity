# Scalar-add literal/storage bridge

Four modules / eight results connect the actual addition helper to the
literal scalar-add Core program and construct the serializer representation
from the actual output loads. This builds on `../scalar-add`'s seven-module
original-C execution checkpoint; it does not replace that execution with a
numerical assumption.

The canonical term is add256 followed by the original one/zero carry
expansion and scalar_normalize512. It reuses the common carry-expansion term
already checked for field addition and the literal scalar modulo port.
Parametricity is proved. The numeric lemmas compare actual limbs with this
term, including inputs normalized by the readers; they are not replacement
public specifications.

`eval_scalar_add_literal_owned` derives actual helper execution, output
writer representation, both 32-byte Freeable regions and outside-memory
framing. Its two reader-value equalities are **internal bridge inputs**. A
public theorem must derive them from two actual reader calls for every input
pair, then compose the actual writer and public entry/copy/return/free.
This checkpoint is not public coverage, registration or full acceptance.

All four final sources compiled. Kernel session **20645** terminated with
exit **0**. Eight types and the one canonical definition were reviewed
untruncated. Dependencies: three closed, two with inherited functional
extensionality, two with four inherited classical dependencies, one execution
result with those plus CompCert external/inline-assembly semantics. The
15-axiom kernel context matches the inherited allowlist exactly; unsafe
categories are empty. No new axiom, admission or unchecked tactic is used.

Scope remains original local-frame / LP64 / RECKLESS, not all evaluator
frames or assertion-enabled execution. Shared registries and production
C/Haskell remain unchanged; Claude's Elements foundation work is separate.
Signed local commits only; no pushes.
