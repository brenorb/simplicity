# Continue from the completed scalar-add public theorem

Last verified declaration:
`AddC.jet_secp_scalar_add_local.scalar_add_literal_local_spec`.
All eight new modules / 19 results / six definitions compile and have terminal
independent kernel/type/assumption checks. There is no failing Coq goal.
Together with prior helper (37), bridge (8), readers (15), the full AddC chain
has **79 checked results**, but no normal registration or coverage addition.

## Next: normal transport, not another caller proof

1. Preserve scalar integration audit **10545**. Original **83287** failed only
   at AST preprocessing because its copied candidate lacked sibling C/Haskell
   source links. Links were repaired after terminal exit 2, reviewer and core
   AST check passed unchanged, and a new full audit was launched. Keep its
   retry log and terminal status. Do not change that candidate's inputs.
2. After terminal full success, pin its receipt with unchanged fingerprint
   `aa652e53f690b80bcdc03a263f11114d04b1e9743f3dac471a41b00e9dac42ec`.
   Partial gates are not acceptance. A frozen reviewed parent may support a
   separate preparation build, but registration requires full acceptance.
3. Construct a **separate** normal-C scalar-add candidate from that immutable
   baseline. Resolve the exact public-root dependency closure of archives
   `scalar-add`, `scalar-add-bridge`, `scalar-add-readers`, `scalar-add-public`.
   Transport `AddC.` to `C.` byte-exactly, reuse byte-identical inherited
   modules, omit unneeded parametric/support modules only by actual closure.
   Preserve sibling source links for AST regeneration before a long audit.
4. Append exact modules/results/definitions and the single scalar-add public
   coverage entry. Freshly compile the closure in normal namespace. Review
   all new printed types/definitions, dependencies and unchanged inherited
   records before generating/accepting expected snapshots. Never silently
   replace earlier expectations or broaden the kernel allowlist.
5. Relocate the literal/public gate and its recursive dependencies explicitly,
   test mutations, then run full normal acceptance without update/no-build
   flags. Only a terminal successful complete audit permits registration.
6. Reconcile accepted prerequisites and scalar-add into the main checkout
   with exact sources/inventory changes, preserving mixed staged/unstaged
   registries, SHA-support and other authors' work. Do not copy a whole scratch
   tree or build products into Git. Isolated coverage is not main coverage.

## Commands and concrete pitfalls

From `/tmp/jet-scalar-integration.XAMDsw/Coq`:

```sh
export PATH=/nix/store/57myhb98wx8k9dr21cf51bsmvxjs67h6-coq-8.17.1/bin:$PATH
ulimit -S -s 65520
bash build-jets.sh --coqc -R /tmp/jet-scalar-add.u1U2Ti AddC /tmp/jet-scalar-add.u1U2Ti/jet_secp_scalar_add_local.v
```

The manifest records the exact independent kernel command/session and every
source hash. The public source includes actual 16/32/32 sizes and an in-place
three-argument helper returning int; field-add's 16/40/40/two-argument/void
adapters are not interchangeable.

An initial writer adapter accidentally destructured the field helper symbols.
The timeout was a **wrong symbol**, not insufficient reduction power. Actual
`Show` exposed `_write_fe` against `_write_scalar`; the final source uses
`scalar_normalize_write_symbols`. Do not extend timeouts or unfold secp_ge
to overcome this mismatch. A generic writer-for-Word256 now avoids redundant
normalize-fixed-point lemmas and can support other scalar arithmetic jets.

Use fresh files for new experiments, leave checked archives and live audit
inputs immutable, inspect actual goals after failures, and preserve memory
facts at the latest state. Shared Elements/linkage/startup/constructibility
work belongs to Claude. Signed local commits, no pushes.
