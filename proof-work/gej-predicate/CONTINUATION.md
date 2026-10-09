# Original Jacobian infinity predicate: internal support

## Latest completed boundary

Flag-accessor independent kernel **39066 passes with exit 0**, 12 inherited
allowlisted context axioms and all three unsafe categories empty.
Three further modules now compile freshly: point reader run **71861** (seven
results), actual execution **57143** (one result, six inherited assumptions),
initial representation **15844** (one result, four logical assumptions).
There are **12 compiled internal results / four modules**, no new public jet.
Reader execution/run independent kernel **73173** is live, log
`point-read-kernel.log`. The initial representation still needs its own
independent kernel receipt; do not include it in 73173's scope.

The field reader uses X/Y/Z offsets 0/40/80 inside a base-zero real local
point allocation of 128 bytes and source local of 16 bytes. It retains the
original field reader body, read event, output cursor invariant, regional
representation and outside-footprint memory framing. Initial field cells are
undefined, not assumed zero. Its representation is now derived directly from
the two Freeable ranges, actual source frame fields and block separation.
No helper call, result value, cursor update or memory change is assumed by
that constructor.

Next extract the normalized coordinate and actual updated source cursor from
the selected point-reader representation, preserving the entire point's
Freeable ownership. Compose three actual reads with cursor rebasing and
other-coordinate/flag preservation. Derive the original Z zero test, flag
store and `read_gej` call, then complete public lifecycle/specification.
The exact public goal and original call chain below remain unchanged.

Public target: `simplicity_gej_is_infinity`, arbitrary GEJ triple input,
Bit output. Canonical CoreJets binds `GejIsInfinity` to the record
`gej_is_infinity = drop fe_is_zero` (LibSecp256k1.hs:510), so only the Z
coordinate controls the result. The implementation nevertheless reads all
three fields via original `read_gej`, sets the flag with original
`secp256k1_fe_is_zero`, reads that flag, writes a bit and returns true.
Do not skip the actual X/Y reads or assume the flag/output/helper execution.

Scratch `/tmp/jet-gej-predicate.W2FtCz`. The three-result support module
`jet_secp_gej_flag_read.v` compiles freshly with terminal exit 0 (68012).
It proves actual entry, exact flag load at base+120 and the entire original
`f_secp256k1_gej_is_infinity` call, including returning the loaded Int value
and freeing its empty locals. Memory is exactly unchanged; base is arbitrary
subject to ordinary point pointer bounds. Flag need not be assumed boolean.
The final accessor has only six inherited execution assumptions.
Independent kernel **39066** is pending, log `flag-kernel.log` in scratch.
Poll that handle before claiming independent kernel evidence.

Reproduce with Coq 8.17.1 and 65520 KiB stack, cwd
`/tmp/jet-negate-accept.ftWsqQ/Coq`:
`bash build-jets.sh --coqc -R /tmp/jet-gej-infinity.YrUC7w C
-R /tmp/jet-gej-predicate.W2FtCz C
/tmp/jet-gej-predicate.W2FtCz/jet_secp_gej_flag_read.v`.
Kernel: same load paths, `--coqchk -silent -o C.jet_secp_gej_flag_read`.

Next adapt the field reader to slices at 0/40/80 inside one real 128-byte
point allocation, not three fictitious base-zero allocations. Reuse the
field-add cursor-rebasing, representation, bit-input and preservation lemmas,
but prove actual arbitrary-offset reader execution and ownership first.
Compose three reads and cursor updates, derive normalized Z's original zero
test and actual flag store, then derive the complete `read_gej` call.
Connect literal `drop canonical_fe_is_zero`, bit writer and the real 16/128
public allocations/source copy/return/free using existing lifecycle contracts.
Only register a whole public theorem after source correspondence, actual
snapshot review, isolated full acceptance and guarded integration.

Observed proof-engineering corrections: helper temps contain `_t'1`, so
parameter/temp disjointness is not vacuous; set the exact field-load location
before rewriting pointer representation; the return-result condition is a
conjunction of nonvoid type and successful cast, not a reflexive equality.
No source, domain, proof-integrity rule or timeout was weakened.
