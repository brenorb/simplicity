# Original C issuance jet, literal primitive program

Source-binding follow-up: this chain does not load the stale Bitcoin module
found during integration review. Nevertheless an incremental make alone is
not a full source/object correspondence check. A separate forced rebuild of
the complete local dependency closure is in `../elements-issuance-clean/`.
Retain the receipts here for their exact compiled inputs; see also
`../original-target-boundary/` for the broader integration issue.

The endpoint is
`C.jet_elements_issuance_status_local.elements_issuance_status_local_spec`.
The five archived complete Coq sources compile against the current checkout,
including the original Bitcoin specification restored to `91d89bac`. They do
not change production C, original specifications, API contracts, generated ASTs
or generation settings. Normal registration/full acceptance remains separate;
this archive does not increment coverage.

The canonical binding is `specificationIssuance Issuance = Issuance.issuance`
in `Haskell/Simplicity/Elements/Jets.hs`. The port follows
`Haskell/Simplicity/Elements/Programs/Issuance.hs`: pair primitive
`ReissuanceEntropy` with primitive `NewIssuanceContract`, then the original
nested `match`, `flip match` and `copair` program. Coq's `case` is Haskell's
`match`; the flipped match's branch order is resolved explicitly. Both
languages define `copair = elimS iden` and false/true as left/right unit.
The two relevant existing primitive clauses are compared with the original
Haskell clauses: both index the same input, and select an optional hash only
for reissuance/new issuance respectively. This is source correspondence,
not a mechanically proved cross-language translation theorem.

The proof covers every Word32 index and all four outcomes: absent input,
present input without issuance, new issuance (false), reissuance (true).
The logical result contains three encoded cells. The actual enum values are
0, 1 and 2; the verified layout reads it at input-record offset 528 (the
issuance member at 256 plus its type at 272), with input stride 544 and
transaction input count at 696. `elements_issuance_status_shape` proves exact
equality with the unchanged `f_simplicity_issuance` body, not a substitute C
function. The indexed execution support is a proof-only instance using the
actual outer bounds-result temporary `t'3`, instead of the older skeleton's
`t'2`.

The local endpoint derives the real Clight call, success, encoded result,
final cursor and memory framing from initial pointers/count/enum loads and
the existing valid separated-frame contract. It has no cached-hash, result,
execution, nonzero-issuance or zero-initialized-output premise. The enum reload
after the first payload bit is preserved by its derived write effect.
This is not a theorem for arbitrary overlapping API buffers, nor a proof that
the production environment builder establishes the relation.

`RUN.json` binds the exact current inputs, source/object hashes, full 16-result
and 17-definition inventory, and assumption reports. Six results are closed;
the reader-semantic result uses functional extensionality. CompCert expression
helpers use four inherited dependencies, and the seven execution/endpoint
results use the same six inherited dependencies as the existing Clight chain.
No new axiom, admitted proof or unchecked cast is introduced.

Reproduction commands (use a distinct private clone containing the five exact
archives as `.v` files in `Coq/C/`):

```sh
python3 -B proof-work/elements-issuance-status/verify.py compile PRIVATE_TREE
python3 -B proof-work/elements-issuance-status/verify.py kernel PRIVATE_TREE
```

These drivers preserve the existing manifests and add proof roots on the
makefile command line with the project's unchanged load paths/configuration.
Receipts are once-only: inspect an existing launch/process instead of
overwriting it or starting a duplicate kernel run. `CHECKED.json`, when present,
records successful recursive kernel checking and postchecks for those exact
inputs only. Historical receipts are not transferred to changed sources.
