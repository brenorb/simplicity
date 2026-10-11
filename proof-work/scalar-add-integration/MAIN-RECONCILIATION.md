# Read-only main reconciliation checkpoint

`plan-main.py` compares the candidate with the **working tree**, records
staged metadata separately, and writes neither. It does not install or
accept proofs. The candidate still requires terminal full acceptance;
integration then requires a separately verified main checkout.

The checked candidate is `/tmp/jet-scalar-add-integration.RxsuOy/Coq`.
Parent acceptance **10545** has now terminated with exit 0; its receipt is
`../scalar-integration/ACCEPTANCE.json`. Preserve both candidate trees.
No proof/inventory/snapshot input was changed by this check.

## Findings

- 201 new `.v` files, 872 identical existing files, **no source conflicts**.
- Main-only `C/jet_secp_fe_negate_math.v` remains untouched and unregistered.
- Both project inventories append 201 rows. Results append 675 rows;
  definitions append 310; coverage appends eight. Every old inventory row
  remains in order and each main file is an exact candidate byte prefix.
- All 3,733 inherited result dependency records are unchanged. The kernel
  axiom allowlist remains byte-identical.
- All **5,611 inherited contract records are byte-identical and in order**;
  the candidate adds 985 records. No snapshot normalization was needed.

The initial diagnostic falsely reported short-name differences. Short names
are not declaration identities: unrelated modules reuse `be_bytes`, `sem`,
`same` and other labels. A new `u128_field` must not be treated as the old
definition. The corrected comparison keys records by **kind, module, full
inventory name and occurrence**, preserving duplicate legacy rows. It also
handles multi-line Variant/Record printing and a mutual fixpoint's trailing
`for f`, which is not a new Print command. Qualified Bitcoin definitions are
retained rather than accidentally dropped. Any missing/reordered/changed
record is reported; no arbitrary qualifications or terms are rewritten.

`test-plan.py` exercises positive cases and eleven malformed/drift fixtures
in memory, including each duplicate occurrence. This is regression testing
of the planner, not proof acceptance.

## Run / next

```sh
python3 -B proof-work/scalar-add-integration/test-plan.py
python3 -B proof-work/scalar-add-integration/plan-main.py \
  --candidate-coq /tmp/jet-scalar-add-integration.RxsuOy/Coq --summary
```

The full report also lists exact source/metadata hashes and staged metadata
hashes. Recompute against the current dirty checkout immediately before any
application; this checkpoint cannot authorize overwriting later changes.

Gate/coverage-tool differences are append-only additions of the eight secp
registrations and their exact source/contract/negative checks. Inspect the
exact differences again before integration, including new non-`.v` gate
files. Do not copy whole scratch trees or generated build products, or
replace the dirty Git index. Preserve the newer SHA-support work and Claude's
Elements/shared-obligation reservation. See `CONTINUATION.md` for the full
acceptance ordering. Main coverage remains **351/533**; isolated **359/533**
is still provisional. Signed local commits only; no pushes.
