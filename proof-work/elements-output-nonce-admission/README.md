# Literal output_nonce registration and combined407 acceptance

The successor adds `simplicity_output_nonce` to the reviewed406 source
candidate. Snapshot preparation and review alone were not normal acceptance.

## New proof and normal delta

The proof is documented in `../elements-output-nonce/`: an actual-C local
contract against the literal indexed optional-nonce primitive, including absent,
explicit and parity/native-Word256 cases. The shared payload-polymorphic index
bridge supports other widths and sum shapes. Four pure results are closed;
the primitive transport retains functional extensionality, and the C endpoint
retains exactly the six inherited assumptions. No execution/output premise or
new libc model is introduced. The inherited array/pointer representation and
caller-construction/empty-array boundaries remain explicit.

One module contributes six results and five definitions. There are two
mandatory source guards, one exact framed whole-C coverage case and seven new
statement-confined coverage corruptions. Existing sources and all inherited
fixtures remain unchanged. Shared preparation and checkpoint-aware review
engines are reused without changes.

## Combined acceptance over the real401 baseline

This supersedes the earlier plan to install and fully audit every intermediate
402/404/406 tree separately. A full audit checks an entire exact source tree;
the final407 candidate contains all four independently reviewed deltas:

- 402: original C `lbtc_asset` (one jet).
- 404: original C legacy relative-lock getters (two jets).
- 406: original C legacy relative-lock assertions (two jets).
- 407: literal `output_nonce` contract (one jet).

`accept.py` verifies the exact installed401 baseline and all four completed
review chains: sources, unmodified inherited contracts/dependencies, tools,
shared engines, fresh proof objects, full reports, all six actual commands,
their exit statuses and logs, plus each predecessor source fingerprint.
Only then can it launch full407 acceptance once, without update/skip flags.
No intermediate snapshot is represented as an accepted installation. The
combined audit covers all six added jets and all inherited entries, including
recursive kernel checking, assumptions/contracts, negative tests and five ASTs.

The existing main401 audit92989 and isolated402 audit26900 remain live and
must not be restarted or killed. Their inputs stay frozen. The isolated402
result may be archived when it finishes, but no main402 installation is needed
for this combined plan. **Keep main at401 until actual-main401 and combined407
both pass.** Do not launch the older404 audit or install402/404/406 while
following this plan. Completed historical results remain valid evidence for
their exact source trees.

Actual-main401 audit92989 and isolated402 audit26900 have now both terminated
with exit0 and complete acceptance markers. Their receipts/log hashes and
driver/source/installation bindings were independently verified, and full logs
are archived in their respective folders. This establishes actual-main401
acceptance, not an intermediate402 installation. Combined407 audit23810 remains
the required successor audit. Do not restart either completed audit or install
intermediate402/404/406 trees under the combined plan.

The proposed407 registry retains104 explicit `memcpy_model` conditions and126
missing public declarations. The full every-jet goal, caller/domain/evaluator,
library/fidelity and configuration obligations remain unfinished. These
receipts bind the actual dirty/staged base, not a clean-HEAD reproduction.
