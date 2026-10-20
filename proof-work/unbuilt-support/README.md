# Archived support modules that do not compile

These five preserved experiments fail against the accepted tree and are outside
the proof build. Their presence makes no coverage or acceptance claim.

| Module | Why it fails |
| --- | --- |
| `jet_bitcoin_env_constructible` (+ `_distance`, `_indexed`, `_raw`) | Written against the 2026-10-05 Bitcoin edit: it proves the total/fee caches as `total mod 2^64`. The rewound `bitcoin_tx64_env_rep` requires the exact total, so line 183 no longer closes. A repair would use the frozen model's `sigTxTotal{In,Out}Value_bound` to show `0 <= total < 2^64` |
| `jet_secp_fe_negate_math` | Uncommitted experiment from the stopped Codex session; `ring` fails at line 17, and nothing imports it |
