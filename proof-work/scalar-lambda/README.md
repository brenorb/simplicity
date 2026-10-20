# Readonly lambda global and literal specification adapters

Later milestone: `../scalar-lambda-caller` proves the full original jet under
the explicit initialized-global state and preserves that state. Its kernel
check is complete; normal registration and initialization/caller construction
remain open. The helper evidence below is unchanged and remains historical.

Checked helper progress only: **no public lambda equivalence or new coverage**.
The all-533 goal remains unfinished.

The original `secp256k1_const_lambda` symbol is resolved through `Genv`, not a
hardcoded block number. From actual `Genv.init_mem jets_secp.prog = Some m`, the
proof establishes valid readable storage and all four exact Mint64 loads.
Separately, no offset in that initial block permits Max Writable. The limb
value is exactly the pinned Haskell `lambda` literal; no mathematical claim
about lambda being a cube root is substituted for C-to-specification work.

The mixed-rho adapter preserves the input's first four words and gives the
borrowed-rhs helper the initialized global's four words. Its region has
`rw=false`, `rfree=None`. Initialization is preserved through actual allocation
and unchanged-on memory. No permission to overwrite/free the global is assumed.

The literal port retains `scalar_lambda = scribe256 lambda` and
`(unit >>> scalar_lambda) &&& iden >>> scalar_multiply`. Parametricity is proved.
The value bridge explicitly reconciles C's normalized-input-times-lambda order
with the canonical term's lambda-times-input order. These numeric lemmas are
internal bridges, not final replacement specifications.

## Verified evidence

Three modules / 20 results / eight definitions. Thirteen results are closed;
five representation lemmas inherit four existing classical/extensionality
dependencies; two numeric adapters inherit functional extensionality only.
All sources compile through final Qed. Global and literal roots each passed
independent whole-dependency kernel checks; inherited 15-name context unchanged,
all unsafe categories empty. Untruncated reports cover all 28 type/definition
records (global 52,195 bytes, literal 4,467 bytes). Manifest and review receipt
pin exact sources, objects, drivers, reports and logs. No main registration.

## Reproduce / continue

Next compose the real jet reader, borrowed scalar_mul call, writer and private
local cleanup. Discharge disjointness from actual fresh allocation and retain
global state through the caller, rather than assume these facts publicly.
`init_mem = Some m` here is a conditional initialization lemma, **not a proof
that the entire secp program's initialization succeeds**, nor an evaluator
lifecycle invariant for arbitrary later callers. Those boundaries remain open.

Avoid the diagnosed expensive conversion: the concrete Clight genv projection
must be rewritten with `scalar_lambda_genv_projection` before applying the
generic `Genv.init_mem_characterization`. Otherwise conversion expands the
entire generated program and hits the ten-second tactic limit. Explicitly
`change` the `word_modulus 8` bound when bridging `to_fromZ`; do not broadly
reduce open numeric/memory goals.

Main is independently auditing as 22185; freeze its inputs and poll that actual
handle. Main's 361/533 registration is not yet full-main acceptance. These
scratch helpers intentionally do not change that count or overlap Claude's
shared/Elements environment reservation. Local signed commits only, no push.
