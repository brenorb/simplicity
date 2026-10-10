# Original point negation: verified boundary and self-copy support

## Latest owned-prefix milestone

**22 freshly compiled internal results / eight modules**. Complete prefix
whole-closure kernel **54432 passes, terminal exit 0**, with 12 inherited
allowlisted context axioms and all unsafe categories empty. This covers all
nine new prefix/field/flag results, not just their compilation. All earlier
17 results now have independent whole-closure kernel evidence.

Original weak-normalizer coordinate execution (36612) compiles, exit 0, five
new results. `eval_point_weak_from_owned_region` uses the original
`f_secp256k1_fe_normalize_weak` at X/Y/Z offsets 0/40/80 in the same actual
128-byte point, retaining its exact final regional representation and framing;
no helper call is assumed. This does not yet assert unchanged canonical
limbs. Independent weak execution whole-closure kernel **74014** is live,
`weak-kernel.log` in scratch; poll its recorded handle before claiming that
receipt. Keep existing point support load paths/dependencies unchanged.

Next derive canonical final limb values and whole-point ownership from the
weak state (carry inputs vanish for the reader's normalized limbs), then
derive the original magnitude-1 negate call at Y offset 40 and compose the
exact owned prefix/helper entry. Do not replace weak normalization with the
strong normalizer. Public writer/lifecycle/literal source/acceptance obligations
remain as listed below. Historical milestone paragraphs retain their original
counts and running-state notes; this top section is the current status.

**17 freshly compiled internal results / seven modules**. New field-address/
owned field-assignment module (53693) and three-copy composition (93553) both
compile, exit 0. Their whole closure kernel **86084 passes, exit 0**, with
12 inherited allowlisted context axioms and all unsafe categories empty.
The concrete field assignment derives the original `_r`/`_a` lvalues/rvalue,
By_copy assignment and store from a real 128-byte Freeable point, valid cursor
bounds and alignment. It applies uniformly to X/Y/Z at 0/40/80; no execution
or preservation premise is assumed. Self-copy requires equal argument
addresses, exactly as the public jet calls this helper, not a public input
restriction. All three stores retain global observable contents and ownership.

Actual helper entry/temp lookups and owned flag-prefix module (30497) compile,
exit 0; the entry retains the generated undefined `_t'1`. The flag prefix
derives its original load and real store, retains the typed flag/Freeable
range and preserves other loads/permissions. The final prefix module (23166)
compiles, exit 0: exact generated body plus composition of flag prefix and
all three self-copies, retaining the flag and owned point before Y arithmetic.
Its outside-flag load frame is for **valid pre-existing blocks**, matching
the memory-framing contract, not a claim about arbitrary invalid/new blocks.
All new execution theorems have the six inherited execution assumptions.

Independent complete prefix whole-closure kernel **54432** is running.
Log `prefix-kernel.log` in
scratch. Do not treat compilation as kernel evidence until terminal exit 0.
The existing eight-result receipts below remain valid. No public coverage or
whole public equivalence is claimed by these internal results.

Next prove the **actual Y weak-normalize and magnitude-1 negate calls at
offset 40** from the reader's normalized field. Compose with this exact owned
prefix and helper entry; then generalize the real three-coordinate writer
and complete the canonical public lifecycle. Do not add a strong normalizer
call in place of the original weak one, assume helper execution, or replace
the target literal program with an integer formula.

Proof-engineering corrections: an unconstrained assignment location did not
infer the base/delta; inspect the leaf and set both source/destination pointers
explicitly. Coq's `n > 0` and `0 < n` are propositionally equivalent but not
convertible in this interface; retain the constructor's exact premise shape.
The framing proof needs initial block validity, rather than inferring it from
a possibly None load. None loads do not by themselves establish validity.

Eight internal results in three modules compile freshly and pass independent
whole-closure kernel checks. These are not a
complete public equivalence theorem, and do not increase registered coverage.

Scratch: `/tmp/jet-gej-negate.IMImaX`; dependencies are the accepted negation
baseline and exact archived infinity/predicate overlays. Sources are kept
outside the checkout's frozen Coq inputs and archived here with hashes.

The actual `f_simplicity_gej_negate` boundary has the same generated declarations
as point infinity (no temporaries). Its real 16/128 entry is derived using
`function_entry2_same_declarations`, not an assumed allocation/entry. The exact
generated body is proved equal to source-copy, original `read_gej`, original
in-place `secp256k1_gej_neg`, original `write_gej`, and true return. Symbol and
call adapters are proved. The remainder composition deliberately retains three
call premises; the eventual owned/public theorem must discharge all of them.

`secp256k1_gej_neg` copies the flag and X/Y/Z before weak-normalizing Y and
negating it with magnitude 1. The public caller passes the same point address
as both arguments. The existing symbolic executor only accepts By_value
assignments, not these By_copy field assignments: do not try to compute the
whole helper with that executor or silently skip its copies.

`self_copy_setN_getN` proves pointwise byte preservation. It does not assert
finite-map or memory-record identity, which can fail because stores insert
explicit entries equal to defaults. `self_copy_storebytes_unchanged` instead
derives `Mem.unchanged_on (fun _ _ => True)` for actual load/store at the same
address. Both are closed under the global context.
`assign_loc_owned_self_copy` derives actual `assign_loc_copy`, the successful
store and global observable preservation from ordinary writable storage,
By_copy type, nonnegative size and alignment. No successful store/execution/
preservation premise is assumed. Its four inherited logical assumptions are
from CompCert's memory existence machinery; no new axiom is introduced.

Independent kernel **81577** for the boundary and **54367** for owned self-copy
both passed with terminal exit 0. `boundary-kernel.log` has the exact unchanged
15-name allowlist; `self-copy-kernel.log` has 12 inherited allowlisted context
axioms. All unsafe categories are empty. Both logs are in scratch; hashes and
actual context axiom lists are recorded in `KERNEL-REVIEW.json`. These are
closure-level summaries, distinct from the per-theorem assumption reports.

Next:

1. Derive the helper's actual flag load/store and three self-copy statements
   from whole-point Freeable storage. Wrap `assign_loc_owned_self_copy` with
   actual field lvalue/rvalue derivations (X/Y/Z offsets 0/40/80, 40-byte fields).
   Preserve loads/permissions/invariants through the returned memory; do not
   substitute record equality or silently reuse old-memory loads.
2. Prove original weak-normalize and negate calls at Y offset 40, then the
   complete in-place helper. Reuse field-negate limb/normalization lemmas but
   retain its magnitude 1 and actual call sequence. No replacement production
   normalizer call may be added.
3. Generalize the point writer from its special infinity payload to arbitrary
   canonical fields, using the actual three original writes and cursor/ownership
   preservation. `write_gej`'s old comment mentions zeroing infinity, but the
   actual C/generated body unconditionally writes X/Y/Z; follow the body.
4. Compose verified owned reader, helper and writer with public entry/setup/
   true return/free. Target literal canonical `gej_negate = take ge_negate &&&
   drop fe_normalize`, with `ge_negate = take fe_normalize &&& drop fe_negate`;
   use the existing literal negation port, not a numeric substitute or narrowed
   point domain. Add source correspondence, inventories, actual audits and
   isolated full acceptance before registration.

Reproduce with Coq 8.17.1 and 65520 KiB stack, cwd
`/tmp/jet-negate-accept.ftWsqQ/Coq`:

```sh
bash build-jets.sh --coqc \
  -R /tmp/jet-gej-infinity.YrUC7w C \
  -R /tmp/jet-gej-predicate.W2FtCz C \
  -R /tmp/jet-gej-negate.IMImaX C \
  /tmp/jet-gej-negate.IMImaX/jet_secp_gej_negate_boundary.v
```

Compile self-copy then assignment with the last overlay; they do not depend
on point predicates. `--coqchk -silent -o` with the corresponding module and
same needed load paths is the independent kernel command. Every proof tactic
keeps the 10-second default; only final assumption reporting uses 60 seconds.
The checkout's full acceptance 86431 remains live on unchanged inputs; no
second whole build or checkout metadata mutation is authorized by this work.
