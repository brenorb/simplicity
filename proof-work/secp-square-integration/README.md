# Square proof integration into ordinary Coq modules

The ordinary endpoint is
`C.jet_secp_square_local.fe_square_local_spec`, with the same general public
frame contract, original `f_simplicity_fe_square`, and literal Simplicity square
term as the checked private endpoint in `../secp-square-public`.

This packet materializes the exact checked source closure as ordinary modules:
223 inherited local sources and 16 mechanically renamed square modules. The
source bytes come from committed blobs, with older dependency reconstruction
bound to the exact checked hashes. The new module rename is exactly reversible;
it does not change statements, proof tactics, C bodies, specification values,
generation settings, or kernel checking.

Only a new external candidate is written. Main proof sources, shared registries,
unrelated staged work, and previously checked trees/receipts are preserved.
Neither private namespaces nor copied local `.vo` files are permitted in the
ordinary build. Existing pinned external Coq/CompCert/VST dependencies are reused.

## Verification protocol

Run from the repository root:

Preparation and audit launches are one-shot. Poll their original processes;
an observation timeout is not a failed build or permission to restart it.
Do not edit audit inputs while a command is running.

The ordinary `coq_makefile`/`make` dependency graph builds the exact 239-module
closure from source. The report stage prints all 90 result types, 55 definitions
and their complete assumption profiles, comparing them to the original checked
reports. Only whitespace and known, unambiguous module-printing aliases are
normalized. Mathematical terms, hypotheses, output conditions and assumption
sets must otherwise be identical. The complete loaded local closure must match
the preparation, without private square namespaces.

The same stage checks all 240 frozen production/canonical/configuration inputs,
the square endpoint/statement/callee wiring and twelve negative mutations. It
also runs the unchanged `C/check-secp-jets-generation.sh`: the secp Clight AST
is regenerated in a fresh temporary directory with the pinned configuration and
compared byte-for-byte with the proof target, without overwriting that target.
The recursive kernel audit retains the exact inherited library-axiom baseline
and requires empty unsafe-kernel categories.

## Receipt and acceptance boundaries

Receipts are bound to their exact candidate sources, objects, project files,
scripts, committed originals, reports and main/staged inputs. The assembler is
a committed-source reconstruction recipe, but the receipts themselves describe
only their recorded run, not all future clean-checkout builds.

This packet does **not** register or accept new shared coverage. The earlier
normal registration attempts in `../secp-field-acceptance` and
`../secp-beta-acceptance` terminated at the frozen Bitcoin `LockTime` identity
discrepancy. Preserve that evidence; do not bypass the gate, correct a frozen
specification without authorization, or rerun the unchanged failure as proof of
new acceptance. The square theorem and the goal of proving every C jet are
distinct milestones; the broader goal remains unfinished.
