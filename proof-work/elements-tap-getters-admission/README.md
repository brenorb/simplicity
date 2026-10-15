# Two Elements tap getters: normal-registration candidate

Proposed successor: **401/533**, over the reviewed 399-jet source predecessor.
Only `internal_key` and `tappath` gain entries. The three checked endpoint
versions in `../elements-tap-getters/` represent two jets, not three.

Candidate: `/private/tmp/jet-tap-getters-admission.ouwiobpu`.
Reviewed candidate input:
`c86dfb5924df9474a3168b5923c508f236576737c3fbb18b9d59a40afaa3752d`.
Main was **386/533** at preparation and has since advanced through the guarded
399 installation. This 401 candidate itself is not installed or fully accepted.

## Source provenance and the explicit inherited-source change

Objects were APFS-copied exclusively from the completed, independently checked
tap-getter proof tree (`2a6bde9f...`). The 399 predecessor supplied only
fingerprint-bound source text, never compiler objects from its live audit.
Assembly and normal preparation leave main and the entire original index alone.
The only permitted main checkpoints are the exact recorded 386 source or the
exact 399 successor, not arbitrary drift.

Six previously unregistered modules are added to the normal public manifests:
the generic hash getter, its writeHash implementation, the hash-field jets,
the original tappath execution module, its nullable variant, and the literal
adapters. There is one new proof source and two deployed source/negative guards.

Unlike the earlier purely additive getter batches, this candidate explicitly
generalizes one inherited **unregistered** source:
`C/jet_elements_tappath_nullable.v`. `ASSEMBLY.json` binds its exact old/new
hashes; no other inherited implementation source may change. Its old nullable
predicate remains definitionally the original <=128 relation. The original
theorem is retained at 128, with the added byte-length endpoint at 255. A formal
compatibility theorem contains the complete old predicate, and the source guard
also pins it. The C proof body changes only its local numeric bound; no new
execution/output premise is introduced. Main's old source is not changed by
preparing this candidate.

The three memory-representation compatibility lemmas retain four inherited
assumptions; they are not axiom-free. Only the four word/key/list conversion
lemmas are closed. All C endpoints retain the same six inherited assumptions.
An initial review check incorrectly expected those compatibility lemmas to be
closed; actual assumption inspection corrected that expectation and the proof
folder documentation. No proof, statement or assumption set was weakened.

## Completed preparation and snapshot review

The whole normal build and six explicit fresh module compilations passed.
The actual normal printer produced 38 added theorem types and 19 definitions,
with complete deep reports for all 57. Every one of the **8,282** inherited
contract records retains its bytes and order, and all **5,444** inherited
dependency sets are unchanged. Eight compact records contain elisions; their
complete deep records are checked against every fragment and retained.

The coverage rows point to the original internal-key C endpoint and the added
nullable-u8 C endpoint. Mandatory source guards also check their formal literal
specification transports, full representations, original-128 compatibility and
raw native Word256 versus byte-index Haskell correspondence. The coverage gate
is extended only for these two exact whole contracts, with 14 statement-confined
negative fixtures; existing fixtures and allowances are preserved.

The read-only snapshot review passed:

```sh
python3 -B proof-work/elements-tap-getters-admission/review.py review /private/tmp/jet-tap-getters-admission.ouwiobpu
```

The **finish workflow 27354 terminated with exit 0**, passing all six stages:
coverage, coverage tests (including 14 new statement-confined fixtures), ordinary
contract comparison, source correspondence, 50 source corruptions and 29
admission/evidence corruptions. `REVIEW.json` binds the successful commands/logs,
source input, tools and 1,252 report/object hashes. `FINISH-CHECKPOINT.json` records
an additional independent check of every bound evidence hash. Its historical
launch (already completed; do not repeat it):

```sh
python3 -B proof-work/elements-tap-getters-admission/review.py finish /private/tmp/jet-tap-getters-admission.ouwiobpu
```

The complete new type/assumption reports, all six stage logs and review receipts
are archived here. The earlier `PREPARATION-CHECKPOINT.json` preserves the
historical pre-finish state, not a second or conflicting acceptance. Snapshot
generation, a completed finish review and the scoped proof-folder kernel checks
still do not constitute full normal acceptance.

## Predecessor, start guards and remaining acceptance

The actual-main 386 audit **92335** and isolated 399 audit **61966 both passed**
with exit 0, including all acceptance gates. The guarded 399 source-only
installation/postcheck also passed, preserving the complete old index and exact
accepted source identity. Its distinct actual-main acceptance is the next
predecessor step. Keep completed candidates immutable; never repeat their
completed audit commands or copy objects from future live audits.

`accept.py` is prepared here but **has not been launched**. It requires this
candidate's completed bound review, real full isolated 399 acceptance, guarded
399 installation and its passing postcheck at exactly `50f56ff9...`. Its own
full audit may run alongside actual-main 399, but installation of 401 must also
wait for actual-main 399 to pass. The two-stage predecessor rule does not allow
calling preparation or scoped kernel checks normal acceptance.

Three negative-only start checks passed without launching a subprocess or
attempting writes. `START-GUARD.json` binds their driver, test and log. These
are refusal tests, not an invented positive acceptance.

Only after all start prerequisites and the completed finish review, launch
the following **once** and retain its handle:

```sh
ulimit -s 65520
python3 -B proof-work/elements-tap-getters-admission/accept.py /private/tmp/jet-tap-getters-admission.ouwiobpu
```

There is no 401 installer yet. After successful isolated 401 and actual-main
399 acceptance, prepare a guarded installer that explicitly permits only the
reviewed nullable-source change, not just new files. Review/install the exact
source delta, preserve unrelated edits and the entire old staging, copy no
objects, run its composed postcheck, then run distinct actual-main acceptance.

This proposed registry retains the 104 explicit `memcpy_model` conditions;
132 public declarations would still be missing. LP64/RECKLESS, represented
environments, global/fidelity/evaluator/domain obligations and host-library
boundaries remain explicit. These are C-to-specification contracts, not proofs
of caller cache construction. The full every-jet goal remains unfinished.
