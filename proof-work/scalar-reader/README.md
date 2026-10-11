# Original scalar reader body and reduced value

Six freshly compiled `OriginalC` modules contain 31 internal results. The
strongest is `exec_scalar_reader_body_numeric`: execution of the **original
body of `f_read_scalar`**, both actual C calls, NULL cast, original setter
branch, four reduced-limb loads, big-endian value modulo the group order,
frame invariant/preservation, and retained Freeable ownership of the buffer.
The body is never replaced. The theorem starts in the actual three-region
allocated context and does not assume the desired calls, output or framing.

This is **not** a complete reader function or public jet equivalence theorem.
Function entry, buffer allocation, void return and buffer free still need
composition around the proved body. `scalar_reader_allocation` verifies the
symbolic allocation layout; it is not alone a concrete allocation theorem.
The scalar/source caller regions are owned 32/16-byte zero-base blocks. The
public jet must derive these and the frame hypotheses from its own lifecycle.
Public coverage added: zero. Registered checkout coverage remains 351/533.

## Reusable structure and a diagnosed dead end

- `jet_secp_pure_oracle_frame`: transport an already-proved actual-C oracle
  to a disjoint external invariant, using symbolic separation and the real
  returned frame. Its abstract correctness/log hypotheses are discharged by
  the concrete shift oracle; they are not new public assumptions.
- `jet_secp_shift64_frame`: successful shift calls have tag zero; nonwrite
  events leave the frame invariant neutral. Actual shift execution comes
  from the independently proved original helper.
- `jet_secp_scalar_reader_run`: the actual first read8s call, byte variables
  1..32, cursor advance by 256, unchanged caller temps and three-region shape.
- `jet_secp_scalar_reader_set`: original setter entry/prefix/NULL suffix in
  that context, then the original second reader call including its cast.
- `jet_secp_scalar_reader_value`: value-preserving expression substitution
  and pointwise byte reindexing reuse the verified setter arithmetic. No new
  function-extensionality assumption is needed for the numeric bridge.
- `jet_secp_scalar_reader_body`: compose the actual statements, derive
  external-invariant stability and framing, expose loads/value/buffer ownership.

Do not retry whole-function `xfun` here: its current `xcast` rejects int-to-NULL
pointer casts and `xbool` rejects pointer conditions, so the unchanged reader
returns `None` in that executor. These are executor limits, not C failures.
The manual original-call/NULL-branch adapters avoid changing the executor or
the C AST. Keep `secp_ge` opaque when resolving the final helper pointer;
broad reduction of its huge generated environment times out. Use the proved
symbol/function lookup and a targeted `change` instead.

## Verification and continuation

All six current sources compile with Coq 8.17.1, pinned CompCert/VST, stack
65520 KiB. The 31 types and 23 non-tree definitions (including five local
frame aliases) printed without truncation and were reviewed. The independent
kernel, exact per-result dependency reports and diagnostic tree printing are
running; see manifest sessions. Until terminal receipts exist, this archive
does not claim independent kernel success or full acceptance.

Sources and drivers are `.source` archives outside accepted load paths.
Materialized modules and logs are in `/tmp/jet-scalar-reverify.8hswEF`; invoke
`build-jets.sh` from `/tmp/jet-ge-negate-accept.5mtyZa/Coq` with the narrow
`-R /tmp/jet-scalar-reverify.8hswEF OriginalC` mapping. The frozen affine
acceptance candidate has not been edited by this work.

Next: use `xalloc_sound` with `scalar_reader_allocation` and the real
`fn_vars f_read_scalar`, establish entry temps/env and extended separation,
apply the numeric body theorem, use its retained buffer ownership to prove
actual local free, and retain only the scalar/source regions. Do not assume
the free, call or representation transition. Then prove public scalar_is_zero
against its literal canonical term (including raw zero OR group-order input),
with source/parametricity gates and normal full acceptance.

SHA startup and memcpy remain reserved for the coordinated Claude session.
All commits and work remain local; no remote pushes.
