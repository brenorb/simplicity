# Point-negate source correspondence

The supplemental gate and all **41 negative mutation fixtures pass** on the
original checkout C/Haskell and the current scratch proof candidates. They
check both jet catalogs, the literal GE/GEJ program expressions, exact final
public theorem, actual C read/helper/write bodies, both application jet-node
bindings, allocation sizes, initial temporaries, and lifecycle composition.

The gate is not a Haskell compiler, a transitive source-fidelity certificate,
an AST audit, or a kernel check. Existing field-normalize/field-negate gates
and pinned AST/source/configuration checks remain required. Reusing the
field-normalize temporary environment is justified by the checked original
function-entry declaration equality, not by similarity of C source.

Reproduce after materializing the archived checker/test `.source` files to
their `.py` names in the candidate directory:

No production C/Haskell changes, snapshot update, or public coverage entry
is authorized by passing these supplemental checks. Full contract review
and isolated acceptance remain open.
