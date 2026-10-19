# Original beta global and multiplication-helper bridge

Follow-up: `../clight-internal-frame/README.md` records a checked-source
extension addressing the conservative multiplier framing described below.
Its own receipts determine its completed verification status; this packet's
historical checked sources and receipts are unchanged.

This is incremental proof support for `FeMultiplyBeta`, not a registered public
jet equivalence. Production C, specifications, primitive identities, API and
generation settings remain the original `91d89bac` targets. Coverage added: zero.

The four archived sources are compiled as `BetaGlobal.{Global,Inputs,Spec,Call}`
in `/private/tmp/jet-secp-beta-global.VsIuk6`, against the previously source-built
ordinary field basis and checked borrowed-operand extension. The verifier
checks those exact sources and objects, not a replacement implementation.

- `Global`: derives the actual symbol and five word loads from
  `Genv.init_mem jets_secp.prog`; proves exact readonly permission bounds,
  the field-radix value and limb bounds; proves that this initialization really
  succeeds, using the generic `program_initialization_checked` theorem.
- `Inputs`: builds the borrowed RHS region and input representation from
  normalized reader storage and the global. The Word256 argument is unrestricted.
  Distinctness of the writable local from the readonly global is derived from
  their incompatible permissions, not imposed as a new public input condition.
- `Spec`: ports the pinned `fe_beta`/`fe_multiply_beta` wiring without changing
  operand order. The literal specification uses `(beta,x)`; the implementation
  uses `(x,beta)`. A proved modular-arithmetic equality connects them, including
  the reader's normalization of an arbitrary Word256 input.
- `Call`: invokes the actual original `secp256k1_fe_mul` wrapper and inner C
  body, including their actual local allocation and freeing. It derives output
  loads, ownership representation, limb bounds and equality of the existing
  writer-output function to the literal specification. It does **not** execute
  `write_fe` or the public `simplicity_fe_multiply_beta` entry point.

The fresh report covers 29 results (including three generic initialization
lemmas) and 16 definitions: 20 results are closed, six have the four inherited
classical/extensionality assumptions, two retain dependent functional
extensionality alone, and the actual C-call result retains exactly the same
six inherited Coq/CompCert assumptions as the borrowed multiplier. No libc model
or new external-function-properties premise is introduced.

```sh
python3 -B proof-work/secp-beta-global/verify.py compile
python3 -B proof-work/secp-beta-global/verify.py kernel
python3 -B proof-work/secp-beta-global/verify.py check
```

The first two phases are one-shot; their launch files are not success receipts.
`RUN.json` records completed fresh compilation and full reports. Only a completed
`CHECKED.json` records a successful recursive kernel run. `check` is read-only
and validates the exact current source/object/log identities, unchanged checkout
inputs and preserved staged patch. The source review checks the original Haskell
constant and wiring against the literal port; this is not a Haskell compiler
correctness theorem. The reused literal multiplication bridge remains the one
from the previously checked field basis.

## Remaining public-jet obligations

Compose real by-value frame entry/copy, `read_fe`, the proved multiplication,
actual normalization/serialization by `write_fe`, return conversion and freeing.
Establish and preserve the initialized-global invariant through those operations.
Prove the entire public frame/memory contract against the literal specification.

The current helper's load frame is conservative: it excludes **both** operand
footprints. A public input buffer may alias the readonly global; excluding that
layout merely to obtain `xsep` would narrow the existing contract. Also, five
preserved Mint64 loads alone do not prove preservation of arbitrary reinterpreted
loads or raw memory fragments. Recover precise preservation from actual writes
or a suitable proved memory invariant. The existing fully generic readonly
execution framework adds two inherited external-properties assumptions; do not
silently introduce that dependency or label it the same six-assumption result.

The unrelated frozen Bitcoin identity/value-domain failures remain unresolved.
Neither this helper audit nor its recursive kernel check is full-repository
acceptance or evidence that every registered jet builds against frozen targets.
