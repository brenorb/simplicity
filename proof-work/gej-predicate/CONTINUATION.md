# Original Jacobian infinity predicate: internal support

## Coordinate zero-test and flag store

**38 compiled internal results / twelve modules**. Three-reader whole-closure
kernel **37831 passed, exit 0**, with 15 inherited context axioms and all
unsafe categories empty. Zero execution compiles (2198 exit 0, six results),
canonical owned-coordinate zero compiles (84611 exit 0, three results), and
the actual final flag assignment compiles (47932 exit 0, two results).
Final execution theorems have the same six inherited execution assumptions;
no new assumed declaration or libc model is introduced.

`eval_point_zero_canonical` derives the original `fe_is_zero` call at any
coordinate offset 0/40/80 within the same real 128-byte allocation. It returns
the canonical `canonical_fe_is_zero` bit for every Word256 input, retaining
whole-point Freeable ownership and outside-point memory framing. Its initial
representation and numeric-to-canonical bridge are discharged, not premises.
`exec_gej_read_flag_owned` derives the generated final assignment from actual
point ownership, loads the stored flag, retains Freeable permissions and
preserves unrelated loads, permissions and valid blocks. It does not take
a successful store as a premise. The lower-level assignment lemma does,
and that premise is discharged by the owned theorem.

Independent whole zero/flag kernel **51921** is live; poll it rather than
restart. Log: `/tmp/jet-gej-predicate.W2FtCz/point-zero-flag-kernel.log`.
Its dependencies are frozen while the check runs.

Next connect the exact original `read_gej` statement/call: use three-reader
composition, zero-test at PointZ, and final flag assignment. Derive source
cursor/frame preservation through zero-test (outside-point frame) and flag
store (other-block loads and unchanged permissions). Then prove the public
predicate's actual source allocation/copy, accessor, one-bit output, true
return and freeing of both public locals. Keep `drop fe_is_zero` as the
literal canonical target, not a numeric substitute. No new public predicate
has been registered from these internal lemmas.

The infinity standard assumption printer remains live (70735). Actual
field-add acceptance remains failed (96671 exit 2) on unchanged tactic
timeouts; retry unchanged inputs serially after heavy printing completes.

## Latest completed boundary

**27 compiled internal results / nine modules**. Owned coordinate reader's
whole-closure kernel **71421 passes with exit 0**, all 15 context axioms
inherited/allowlisted and all unsafe categories empty. Same-point footprint/
coordinate preservation compiles (56485 exit 0, two results), and the actual
three-reader composition compiles (6534 exit 0, two results).
It derives calls at offsets 0/40/80, all three normalized fields in final
memory, the actual source cursor rc+768, both whole local Freeable ranges,
the final cursor/output invariant and each call's precise memory frame.
No call, cursor advancement or other-coordinate preservation is assumed.

The generic preservation helper takes length <=5 for its arbitrary limb
list; `point_canonical_limbs_length` discharges this for every Word256
input, not by restricting the public input domain. Reads use the same
point block; no false assumption of three distinct field allocations.
Whole-three-reader independent kernel **37831** is live, log
`point-three-read-kernel.log`. Do not edit its sources or dependencies.

The older negation scratch baseline lacks the shared field-add rebase module.
An exact copy of `proof-work/fe-add/jet_secp_read_fe_rebase.v.source` is
materialized in the predicate overlay and compiles freshly (83850 exit 0).
This reused module is not counted as a new predicate result. Materialize
and compile it first when reproducing `jet_secp_point_three_reads`.

Next derive original zero-test execution on Z inside the whole point region,
the resulting canonical bit and actual flag store. Connect the exact
`read_gej` body/call, then source allocation/copy, bit output, true return
and freeing both public locals. The literal target remains the canonical
record's `drop fe_is_zero`; do not register this internal three-read
composition as a public jet.

There are now **23 compiled internal results / seven modules**.
Initial-storage independent kernel **96146 passes with exit 0**, all 15
context axioms on the inherited allowlist and all three unsafe categories
empty. New compilers: values/offset bridge **18993** (six results), final
field/source extraction **88519** (four results), owned coordinate call
**53923** (one result), all terminal exit 0. Final-field extraction retains
four inherited logical assumptions; the complete reader call retains six
inherited execution assumptions. No new axiom or libc model is introduced.

The complete `eval_point_read_fe_canonical` derives original `f_read_fe`
execution at the selected coordinate, canonical normalized limb loads,
actual source fields at rc+256, both real Freeable ranges and memory framing
from initial frame/input/storage/separation/invariant facts. It does not take
helper execution, normalized field data, a cursor update or final ownership
as premises. Whole-owned-reader independent kernel **71421** is live, log
`point-read-owned-kernel.log`; its closure includes the new values/final/
initial/run/execution modules. Poll that handle, do not restart on yield.

Next compose X/Y/Z reads using the field-add invariant rebasing lemma, and
prove same-point other-coordinate preservation from the precise field
footprints (do not require different blocks for the three coordinates).
Then derive original Z zero-test call and flag store, `read_gej` call and
public predicate allocation/copy/output/return/free chain. The intended
literal specification remains `drop canonical_fe_is_zero`.
The separately live infinity assumption generator is **70735**, still
progressing through old records. Field-add checkout **96671** remains stopped
on unchanged proof timeouts; serial unchanged-input retry follows heavy
printing. These limitations do not reduce the public goal.

Point-reader run/execution independent kernel **73173 now passes with exit
0**, 15 inherited allowlisted context axioms and all unsafe categories empty, log
`point-read-kernel.log`. This covers the seven run results and actual
execution result, not the separately added initial-representation theorem.
Sources are in signed local commit **9e41f9f2**. Initial representation's
independent kernel **96146** is live, log `point-read-initial-kernel.log`.
Poll this handle; do not restart it.

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
