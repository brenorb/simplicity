# Ordinary-module scalar-lambda candidate

This is an isolated integration of the checked proof in
`../scalar-lambda-internal/`, not a shared registry change or an accepted
coverage increase. The main checkout's production C, original specifications,
API, proof sources and unrelated staged patch are untouched.

`PREPARATION.json` maps the nine `LambdaInternal` modules reversibly to
`C.jet_secp_scalar_lambda_closed_{graph,state,calls,chain,rest,public,initialized,local,fresh}`.
Only qualified module-name tokens change. The new candidate is
`/private/tmp/jet-lambda-ordinary-l9tfmi9g`; neither checked parent tree is edited.

`BUILT.json` records a successful ordinary `coq_makefile`/`make -j2` build of
all 323 local modules, starting from source with **no copied local `.vo`
objects**. The original terminal build logs are archived here.

The ordinary report audit and separate recursive kernel check both passed.
`RUN.json` records exact equality of all 19 complete theorem types, the one
definition and every dependency profile. `CHECKED.json` binds the successful
recursive kernel command and log; `verify.py check` revalidates those exact
inputs. The loaded local closure is exactly the 323 freshly built modules, with
no private namespaces. The existing 15-axiom global library context is
unchanged, with no unsafe kernel flags; each new endpoint depends on the six
inherited assumptions recorded by its own profile.

The intended endpoints are:

- `C.jet_secp_scalar_lambda_closed_local.scalar_lambda_initialized_local_spec_internal`
- `C.jet_secp_scalar_lambda_closed_fresh.lambda_runs_from_actual_init_internal`

The existing initialized local-frame contract and the witness for every
256-bit input starting from actual `Genv.init_mem` remain unchanged. The
checked parent has six inherited dependencies at these endpoints, removing
the earlier proof's two generic external-call property assumptions. This is
not an axiom-free claim. The ordinary audit compares all 19 complete theorem
types, the one call-table definition and every exact per-result dependency
profile against that parent, checks the loaded dependency closure, reruns the
literal-source correspondence gate and regenerates the original secp AST.

Scope remains the original pinned LP64, assertion-disabled (`RECKLESS`) Clight
translation and existing frame/startup contract, not every architecture,
configuration, evaluator setup or every C jet. The frozen Bitcoin identity and
domain blockers of normal acceptance are not bypassed or altered. No normal
acceptance or registration is attempted by this packet.

From the repository root:

```sh
python3 -B proof-work/scalar-lambda-internal-integration/assemble.py check
python3 -B proof-work/scalar-lambda-internal-integration/verify.py kernel
python3 -B proof-work/scalar-lambda-internal-integration/verify.py check
```

Launch guards intentionally reject re-running an already launched phase.
Poll its original process handle; a launch file is not completion evidence.
Receipts are specific to their recorded sources, objects, tools and logs.
Use a new derived tree and receipts for later changes rather than editing a
checked candidate in place. The broader every-jet goal remains incomplete.
