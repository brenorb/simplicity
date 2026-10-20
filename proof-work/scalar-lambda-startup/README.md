# Actual secp startup exists

`LamInitC.jet_secp_scalar_lambda_init_exists.scalar_lambda_initialized_memory_exists`
constructs a witness for **actual** `Genv.init_mem jets_secp.prog = Some m`
whose memory satisfies the initialized readonly lambda representation used
by the checked original jet. This closes initialization existence, not merely
the earlier conditional `init_mem = Some m -> ready m` lemma.

No dummy translation unit, replacement global, external model or assumed
initialization success is introduced. A proved generic checker validates all
real initializers' alignment and pointer-symbol references, then applies
CompCert's `Genv.init_mem_exists`. The boolean check of the unchanged program
is a closed formal proof. Five of six results, including initial-memory
existence itself, are closed; the ready-memory witness inherits only the
existing four classical/extensionality dependencies.

Two modules / six results / four definitions compile through Qed. Build
85489, assumptions 72353, contracts 5510ba and whole-dependency kernel 51885
all exited 0. The ten full type/definition records total 3,913 bytes without
ellipses. Kernel context matches the inherited 15-name allowlist; unsafe
categories are empty. Manifest and receipt pin sources, objects, drivers,
reports and log. Nothing is registered in normal/main coverage yet.

## Diagnosed performance pitfall

Do not compute the whole concrete memory image: repeated byte stores into the
large precomputed tables exceed a speculative ten-second tactic bound.
Alignment/reference checking is far smaller. Keep its soundness lemma generic
in an AST program rather than rewrite a concrete huge program throughout the
proof. Use explicit application and keep `program_initialization_okb`,
`Genv.init_mem` and `jets_secp.prog` opaque during that application: otherwise
conversion eagerly expands/recomputes them. This controls reduction only;
all final proofs underwent normal kernel checking, with no disabled checks.

## Continue toward acceptance

The parent full original lambda proof is `../scalar-lambda-caller`, signed
locally at `4f706818`; it preserves its initialized global state. Historical
parent receipts correctly do not claim this later initializer result.

Fresh input/output/source frames for every input and initialized-state
preservation are now checked in `../scalar-lambda-frames`. This is a logical
CompCert memory construction, not the C evaluator's setup routine. Next finish
normal integration and full acceptance in `../scalar-lambda-integration`.
The generic framing root uses eight already-allowlisted Coq/CompCert parameters;
do not misreport it as the startup witness's four or the older helper's six.

Main audit 22185 is terminal exit 0. Main coverage stays 361/533, with 104
explicit memcpy-model entries, until separately verified lambda integration.
The all-533 goal remains active. Signed atomic local commits; never push.
