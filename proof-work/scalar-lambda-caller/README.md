# Original lambda jet: full call under initialized global memory

Later checked milestone: `../scalar-lambda-startup` now proves that actual
`Genv.init_mem jets_secp.prog` succeeds and constructs its initialized lambda
state. The historical caller receipt below remains unchanged. Fresh caller
frame construction and normal registration/acceptance are still open.

Root: `LamCallC.jet_secp_scalar_lambda_initialized.eval_secp_scalar_lambda_initialized`.
This checked result invokes the **original** `f_simplicity_scalar_multiply_lambda`
and returns the encoded **literal canonical Simplicity** term. It derives actual
entry, both private allocations, source copy, reader, borrowed-global multiply,
writer, return and free. It also preserves the initialized global state for
later callers. No execution, output, arithmetic result or cleanup is assumed.

It is an **unregistered scratch result**, not normal/main acceptance or a
coverage increase. Its `scalar_lambda_initialized m0` precondition includes the
four real lambda loads and exact readonly permission bounds. The real
`Genv.init_mem` establishes this state **if initialization succeeds**. Existence
of the complete secp program's initialized memory and construction/preservation
through the evaluator's real frame setup are still separate obligations.
Do not drop this boundary, or claim the unrestricted old `secp_jet_local_spec`.

## Shared framing improvement

The earlier helper frame excluded readable rhs cells along with writable ones.
The new shared readback theorem derives preservation of readonly bytes from
real Clight2 execution, including actual allocation, stores, calls and free.
Readback alone does **not** promise final readability: an external call can
reduce permissions. `readonly_region_lframe` combines it with proved initial
readonly bounds and final readability to recover full load/permission framing.
The borrowed multiplication derives that readability from its resulting region;
the public caller derives it from actual frame effects. Neither is a new
public assumed output premise.

The reader preserves the global even if the global is an input-frame block:
use the no-write `finv` equality for frame blocks, and the ordinary private-local
frame for other blocks. No arbitrary global/input block separation is added.
Disjointness from private scalar/source locals is derived from fresh allocations.

The unchanged `jet_clight_forward.v` is reused byte-for-byte from the existing
SHA-support archive. New scratch modules are additive and do not edit Claude's
shared/Elements builder work or the main proof registries.

## Verification and assumptions

Eleven modules / 53 results / seven definitions; all explicitly rebuilt in
manifest order through Qed. Thirty results are closed, nine inherit four
classical/extensionality dependencies, two inherit those plus the two CompCert
semantics parameters, and twelve inherit all eight already-allowlisted
Coq/CompCert parameters. In particular, the generic execution-preservation
lemmas use CompCert's `external_functions_properties` and
`inline_assembly_properties`; the final lambda theorem therefore has **eight**
inherited dependencies, not the six of the older multiplication helper.
There is no new axiom or explicit libc-model premise.

Build 69420, assumptions 38849, contracts 2315fc, independent whole-dependency
kernel 97038 all exited 0. Kernel context is the inherited 15-name allowlist;
all unsafe categories are empty. Sixty full type/definition records occupy
43,323 bytes, with no ellipses. Sources, objects, drivers and evidence are
pinned in `manifest.json` and `REVIEW.json`. Archive `.source` files are not
normal build entries; objects are never copied into main.

Run `python3 -B proof-work/scalar-lambda-caller/review.py` and `test-review.py`
from the repo. For Coq reproduction, use the immutable multiplication base's
`build-jets.sh`, Coq 8.17.1 and a 65520 KiB stack. The manifest names the two
scratch mappings (ReadonlyC, LamCallC); dependencies additionally use BorrowC,
BorrowFC, LambdaC and LamSpecC from their respective archives. Rebuild in
manifest order; independent root is the theorem's module above. Keep inputs
frozen while any checker is live.

## Next

1. Close initialization existence and actual caller frame construction while
   retaining the named readonly-global representation. Do not substitute a
   mathematical lambda property for the literal constant or weaken the output.
2. Design/review the initialized-memory public contract and source-wiring gate;
   reconcile normal namespaces, metadata and explicit eight-dependency sets.
   Then run full isolated normal acceptance, not merely snapshot generation.
3. Integrate only after the real main audit is terminal; preserve existing
   staged/unstaged work and previously reviewed contracts.

Main audit **22185** remains independent: log
`/tmp/jet-square-main-audit.BLWJ4e/full-acceptance.log`, fingerprint
`2fd541106f2092a42ca83c65b2bdae777eb6e21ffb40a67ec331e2bb341c6ba0`.
Latest observed gate: all 937 kernel modules passed, assumption gate running.
Main remains 361/533 registered, including 104 explicit memcpy-model entries;
no full-main acceptance claim yet. All-533 goal stays active. Signed local
commits only; never push.
