# Reviewed lambda-to-main preflight (read-only)

Current isolated full acceptance **21530 is still running**. This preflight
does not install anything or increase accepted coverage.

The fresh plan at `/tmp/jet-lambda-main-plan.UQsC0D/PLAN.json` has SHA-256
`0fe30b5d73626935e042fc228c3619cb4350b5559aa6f1714be04209f81c2e5e`.
`MAIN-PLAN-SUMMARY.json` records its exact main/index/candidate boundaries.

Checks: 1,157 identical existing sources; one main-only source preserved;
28 selected new proof modules and two source guards; all 7,299 existing contract
records and 4,814 dependency sets unchanged; project/public/definition/coverage
inventories are ordered byte-prefix extensions. Exactly four gate-script
differences were reviewed: new source/mutation invocations, the named
initialized lambda coverage shape, coverage refusal tests, and Require-only
loading of the new modules in contract printing. No old gate is removed.

`test-plan.py` rejects 22 unsafe proposals, including source/path/contract/
dependency/order corruption, unreviewed addition hashes, wrong fingerprints
and extra coverage. `test-apply.py` rejects four nonterminal/mismatched receipt
fixtures while main/index hashes remain unchanged.

The application command requires a matching terminal isolated
`ACCEPTANCE.json`, complete log/hash, unchanged source fingerprint and
read-only normal review. It then recomputes and exactly matches the recorded
plan before allowing `--apply`; all old sources and index bytes are protected.
No stage/commit/object-copy operation is inside that script.

Recompute the plan after acceptance; do not blindly apply this older observation.
Main remains accepted at 361/533 and its source fingerprint
`2fd541106f2092a42ca83c65b2bdae777eb6e21ffb40a67ec331e2bb341c6ba0`.
The staged patch remains
`f2083389e06d3a5aed12c83d0aae554895eab94eef8e107c5d445f9268d86bbe`.

