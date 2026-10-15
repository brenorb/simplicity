# Project-local rocq-mcp

The tested Coq 8.17.1 backend is installed for this checkout only. No global
Codex registration, opam package changes, or project prover upgrade was made.
This is a debugging interface, not a new jet-equivalence result or acceptance
gate.

## Local installation

Machine-local, ignored files:

- `.rocq-mcp-local/`: the runtime, approximately 1.6 GiB logical size (APFS-cloned
  where possible). Contains the tested backend, Python packages, unmodified
  upstream server, and a seed copy of the trial proof/dependency workspace.
- `.codex/config.toml`: project-scoped server `rocq`, invoking `launch.sh` through
  `/bin/bash`. `rocq_switch` is disabled in Codex to retain the pinned prover.

The compatible runtime was copied from the trial, not resolved against newer
packages: rocq-mcp 0.3.1 at `ee6d2c2d9f7acda80a5a5c893de608763a2597a9`,
coq-lsp/pet 0.2.4-dev at `deac261544b5286cae239d537a4b00af62f7d45f`,
Coq 8.17.1 / OCaml 4.14.1, pytanque 0.2.2, FastMCP 4.1.0.
The Python environment was recreated using Homebrew Python 3.14.7 and populated
with the trial's tested installed packages. Its editable server path now points
to this checkout, not the temporary trial. Nothing launches from the trial's
temporary directory. Reinstallation is required if the ignored runtime is
removed, this checkout moves, or the Homebrew Python ABI changes.

The trial report is in the managed `rocq-mcp-trial` worktree at
`proof-work/rocq-mcp-trial/README.md`. Installation deliberately preserves that
worktree and its temporary runtime.

## Using it

Reload/restart the MCP connection in Codex to discover newly configured tools.
`codex mcp get rocq --json` recognizes it inside this checkout, not from
`/private/tmp`. Project configuration requires a trusted project, as described
in the [official MCP documentation](https://developers.openai.com/codex/mcp).

Call `rocq_health` first: expect Coq `8.17.1 4.14.1` and pet `0.2.4-dev`, with
paths under this checkout's `.rocq-mcp-local`. Then use named-theorem starts,
for example `rocq_start(file="FrameProbe.v",
theorem="eval_frame_edge_ofs_early")`, followed by `rocq_check` and `rocq_query`
with the returned `from_state`. Omit `workspace` to use the server's isolated
default. Relative `Coq/C/jet_read8.v` also exists in that copy.

Each server launch creates its own `/private/tmp/simplicity-rocq-mcp.*` workspace
from the durable seed and reports its path on stderr. Source edits and compiler
outputs stay there, outside the accepted source tree. The seed is the trial's
snapshot, **not an automatically synchronized view of current proofs**. Copy
the intended current source/dependencies into the external workspace and rebuild
changed dependencies before debugging newer work. Do not mix cached objects
compiled with OCaml 4.14.4 with this backend's 4.14.1 objects. The seed includes
CompCert 3.14 objects rebuilt with the matching compiler.

For a reproducible harness, `SIMPLICITY_ROCQ_WORKSPACE` can designate an existing
empty external directory. The launcher refuses repository-local or nonempty
destinations. Session directories are retained for inspection, not auto-deleted;
they may be cleaned by the OS. Do not share mutable workspaces across agents.

Known upstream/backend limitation: preamble-only `rocq_start(preamble=...)`
failed in the trial with `No node at point`. Use named theorems and query from a
live state; retain persistent coqtop as a fallback. The launcher imports
`rocq_mcp.server.main` like the upstream console entry point; running that module
with `python -m` hits a circular-import failure on this version.

Always finish with full `coqc`, recursive `coqchk`, and the project's existing
assumption/canonical-fidelity/acceptance gates. Never use `mode="vos"` as proof
verification. `rocq_compile_file` cleans artifacts by default; use
`mode="full", keep_vo=True` when consumers need its object. Reopen live states
after rebuilding dependencies.

## Installation check

```sh
.rocq-mcp-local/venv/bin/python proof-work/rocq-mcp/smoke.py
```

This uses a real MCP stdio client, checks the pinned binary versions/paths,
replays the exact `eval_frame_edge_ofs_early` statement/proof from the current
`Coq/C/jet_read8.v`, deliberately tests a wrong tactic and recovery from its
last valid state, queries a CompCert constructor, completes `Qed`, fully
compiles, and independently runs recursive `coqchk`. It adds no axioms or proof
shortcuts. Inherited assumptions are reported, not silently reclassified as
axiom-free. Raw results and source hashes are stored locally in
`.rocq-mcp-local/smoke.json`; stderr is in `smoke-stderr.log`.

Only this launcher, harness and documentation are versioned. Runtime binaries,
machine-specific Codex configuration, copied proofs and build outputs are not.
