# Actual Bitcoin environment composition and frees

This supporting batch adds exactly five frozen files from Claude commit
`30404face45383153528f36d915de6d7df11f3f4`: `jet_bitcoin_env_txenv`,
`jet_bitcoin_env_txenv_link`, `jet_bitcoin_env_build`, `jet_bitcoin_env_free`,
and `jet_bitcoin_env_lifecycle` under `Coq/bitcoin-env/C`.

The chain is actual C `build_txEnv` execution -> canonical `sigAllHash` ->
`build_environment` (the transaction, taproot and txEnv calls, in their actual
successive memories). The composition result supplies fresh distinct builder
blocks, `env_ready`, preservation of old memory outside the destination, and
the size headers/freeable permissions used by `free_environment`. The free
wrappers call CompCert's defined `EF_free`: no external free model is added.
The wrapper theorems cover returned non-null allocations, not `free(NULL)`.

Run `python3 -B proof-work/bitcoin-composition-integration/run.py prepare`,
then `check --candidate DIR`, then `install --candidate DIR`.
Use `ulimit -s 65520`; the checker selects Coq 8.17.1 and CompCert 3.14.
Only source-matched, hash-pinned objects from the checked transaction unit
are reused. New modules compile, the production AST is regenerated, all
derived-builder theorem assumptions/types/definitions are reported, and both
roots are kernel-checked with their dependencies. Existing assumption records
must remain identical. The normal registry and the user's staging are untouched.

Program boundary: the isolated `C.jets_sha` is the environment program, not
main's original SHA/jet program. Sources remain outside the normal C load path.
This batch adds no jet coverage and is not evaluator/`exec.c` verification.
Original-program caller-to-jet transport, startup establishment/preservation
and the `ready_<jet>` relation sweep remain separate batches.

Construction retains `memcpy_model`, readable raw data and address bounds,
an aligned writable 56-byte destination, and environment-unit SHA startup
facts. The represented Bitcoin environment requires nonempty inputs and a
tap path of at most 128. The raw txid is copied, not computed or validated.
`raw_buffer_at` requires valid non-null data blocks even for empty buffers.
Successful CompCert allocation does not cover system allocation failure.
The arbitrary destination contract does not establish preserved SHA startup
state after construction; later startup preservation needs its separation
conditions. No libc model or input premise is silently discharged here.

`post-check` verifies the exact additive delta from the previous source
fingerprint, all imported blobs/artifacts, and the original staged patch. The
receipts do not claim a new combined normal whole-worktree acceptance run.
