# Read-only main reconciliation checkpoint

`plan-main.py` compares the actual main worktree, its separate staged metadata,
and the frozen multiply candidate. It installs nothing and asserts no candidate
acceptance. `MAIN-PLAN-SUMMARY.json` is a historical observation, not authority
to overwrite a later worktree; always recompute the full plan before applying.

At this checkpoint there are 270 candidate source additions and no conflicting
existing `.v` sources. The main-only `C/jet_secp_fe_negate_math.v` must remain.
All five inventories are byte-prefix extensions: 270 project entries, 1,034
theorem entries, 589 definition entries and nine jet rows. Main's 3,733
dependency records and 5,611 ordered contract records are unchanged; the kernel
allowlist is identical. Candidate 360/533 is still provisional, main 351/533.

Four gate scripts differ and need explicit review, not blanket replacement:
`check-jets.sh`, `jet-coverage.py`, `test-jet-coverage.py` and
`audit-jet-contracts.sh`. The last includes the already-reviewed qualified
import change preserving inherited Print output when internal names collide.
The existing staged/unstaged registry, range and SHA work is not committed or
altered by this planner. Its full output pins staged metadata separately.

The planner reuses the multiply review's exact ordered declaration parser,
including only the three known constructor/parent Print aliases. Positive
duplicate/qualified/legacy fixtures and 14 drift fixtures passed in memory.
This is parser verification, not a new Coq proof or an acceptance gate.

```sh
python3 -B proof-work/scalar-multiply-integration/test-plan.py
python3 -B proof-work/scalar-multiply-integration/plan-main.py --candidate-coq /tmp/jet-scalar-multiply-integration.yIS07H/Coq --summary
```

Omit `--summary` to inspect every proposed addition and staged metadata hash.
Actual integration waits for terminal success of the existing audit **38093**,
unchanged input fingerprint, reviewed overlaps and separate main acceptance.

## Shared-obligation coordination

Claude's `claude/shared-obligations` at reported commit `c3778398` provides
`Coq/C/jet_memcmp_model.v` and the reference `jet_memcmp_impl.v` proof. Future
Elements fee-lookup proofs should use that same explicit `memcmp_model`
premise: unsigned-byte lexicographic comparison sign, `E0`, unchanged memory.
The reference internal implementation does not itself discharge the external
libc premise for an unlinked program. Neither file is registered here.

Claude reserves the remaining Elements transaction-builder work (null-data,
copyOutput/copyInput, sumFees and rsort). This scalar reconciliation does not
overlap it. No changes are made to the sibling worktree or its registries.
