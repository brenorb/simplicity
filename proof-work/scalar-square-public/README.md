# Complete public C scalar square to literal Simplicity

Checked root:
`SqLitC.jet_secp_scalar_square_local.scalar_square_literal_local_spec`.
Its type is exactly
`secp_jet_local_spec f_simplicity_scalar_square (Word 8) (Word 8) (@canonical_scalar_square Alg.CoreFunSem)`.
The target is the literal Haskell `iden &&& iden >>> scalar_multiply` term,
not a substituted square/modulo function. Its Core parametricity is checked.

The proof derives actual public function entry, fresh `src` and `a` locals,
the by-value source struct copy, one real reader, the original
`scalar_mul(a,a,a)` call including its private array allocation/free, the real
writer, true return and both public-local frees. It derives exact literal output
encoding, cursor effects, prefix preservation and the public frame contract.
Only the inherited general local-frame/input/cursor preconditions remain in
the final root: no assumed call, result, normalized storage, output ownership,
allocation or free premises are added.

The shared-pointer product/function proofs are reused from
`../scalar-square-alias` and `../scalar-square-function`; ownership of a scalar
block is never duplicated. The existing reader, serializer, public setup and
cleanup infrastructure is reused. The original C, ASTs and other specifications
are unchanged. This closes **one new public proof**, but it is still a scratch
namespace candidate, not registered/main accepted coverage.

## Verified scope and evidence

Eight results are closed. The normalized-value numeric bridge retains the
existing functional-extensionality dependency. Seven execution results retain
the existing six classical/extensionality/CompCert-semantic dependencies. No
new axiom was added. The dependency-wide context matches the inherited
15-axiom allowlist and all three unsafe categories are empty.

The full untruncated report has 16 types, four definitions and two explicit
critical definitions (the public frame predicate and canonical multiply),
21,816 bytes in total. Source guards check the exact public C function/types/
premise boundary and literal canonical term against the Haskell `mkLib` field.
The separate generic `mapLib` field is not the canonical definition. Twenty-six
in-memory corruption fixtures reject weakened/relabelled/missing boundaries,
reports and receipts without editing proof inputs.

For a fresh rebuild use Coq 8.17.1, `ulimit -S -s 65520`, the existing base
`build-jets.sh --coqc` with the three narrow `-Q` mappings above, and each
absolute `.v` path in manifest order plus both drivers. Capture fresh reports
and terminal statuses. Independent `--coqchk -silent -o` uses the same mappings
and root `SqLitC.jet_secp_scalar_square_local`. Process bounds: 120 seconds per
compile, 900 for the whole-dependency kernel. Stale `.vo` files are not evidence
for edited sources.
