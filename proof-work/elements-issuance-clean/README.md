# Issuance: full forced-source rebuild

This is a new verification run, not a relabeling of the earlier incremental
receipts in `../elements-issuance-status` and `../elements-issuance-constructible`.
It uses the same six complete proof sources without changing C, original
specifications, API contracts, compiler settings or the project manifests.

The forced `make -B` build succeeded and recompiled **242 project modules**.
Full reports check the 22 results and 17 definitions, with the same exact
per-result assumption inventory. `RUN.json` binds that successful command/log,
the current source inputs, new proof objects and unchanged original staging.

`SOURCE-CLOSURE.json` independently checks that the set of 242 project modules
reported by `Print Libraries` is exactly the set of successful-build `COQC`
lines. It hashes every loaded local source and object, not only the six new
modules. The stale Bitcoin module seen elsewhere is not loaded by this chain.
External Coq/CompCert/VST dependencies retain the pinned project runtime/trust
boundary; they are not claimed to have been rebuilt by this local command.

The once-only source-bound recursive kernel launch is in
`SOURCE-KERNEL-RUN.json`; its underlying launch is `KERNEL-RUN.json`.
`SOURCE-CHECKED.json`, when present, records successful recursive kernel
checking and postchecks for the complete exact local source/object closure.
Do not infer success from the launch alone. Normal registration and full
repository acceptance remain separate and zero coverage is added here.

The driver commands are:

```sh
python3 -B proof-work/elements-issuance-clean/verify.py compile PRIVATE_TREE
python3 -B proof-work/verify-forced-closure.py snapshot proof-work/elements-issuance-clean C.jet_elements_issuance_status_constructible
python3 -B proof-work/verify-forced-closure.py kernel proof-work/elements-issuance-clean
```

Use distinct private trees and once-only receipts. Inspect the original process
and terminal state before taking any continuation action. Source/verification
drivers must remain unchanged while their audit is live.
