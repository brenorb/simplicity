# Earlier scalar and uint128 helpers

These distinct earlier sources use the `OriginalC` namespace and remain outside
the active build. Their historical dependency base is
`93542abcf17db8d5b45bdfd7c1e897df39bd3b96`; inspect their imports before
materializing them in an external tree. Some interfaces have since changed.
The literal-source checker has old local paths and needs adaptation before use.

`jet_secp_scalar_overflow_flags` has a known previous compilation failure.
None of these archived files claims fresh compilation or acceptance on the
current branch. The active scalar jet registrations are separate; see
`Coq/C/JET_ACCEPTANCE.md`. Original candidate metadata is recoverable as described
in `../README.md`.
