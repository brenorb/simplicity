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

The seven modules / 16 results were explicitly rebuilt in order after the last
source edit (**96571**, exit 0). Assumption driver **11020**, contract driver
(terminal chunk **72dd23**) and independent whole-dependency kernel **10877**
all terminated with exit 0. Sources were frozen during those checks. `REVIEW.json`
pins sources, compiled objects, drivers, reports and kernel log; the reviewer
also revalidates both prerequisite archives and the immutable dependency tree.

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

Scope remains inherited public **local frames / LP64 / RECKLESS**, not new
assertion-enabled or evaluator/all-frame closure, and not all-jet completion.
The accepted normal dependency candidate's full multiply gate is now complete:
`../scalar-multiply-integration/ACCEPTANCE.json` accepts isolated 360/533 with
four regenerated AST matches and an unchanged fingerprint. This square archive
does not claim a separately regenerated AST or full registry acceptance.

```sh
python3 -B proof-work/scalar-square-public/review.py
python3 -B proof-work/scalar-square-public/test-review.py
```

Scratch: `/tmp/jet-scalar-square-literal.aDYc46` (`SqLitC`). Function/body
dependencies: `/tmp/jet-scalar-square-function.FMkNQs` (`SqrFC`) and
`/tmp/jet-scalar-square.xWr06l` (`SqrC`). Normal frozen dependency tree:
`/tmp/jet-scalar-multiply-integration.yIS07H/Coq`, fingerprint
`1b159005caeac45684fe3b38d56f46bd78a166845fa62fc365137cafe82c3669`.

For a fresh rebuild use Coq 8.17.1, `ulimit -S -s 65520`, the existing base
`build-jets.sh --coqc` with the three narrow `-Q` mappings above, and each
absolute `.v` path in manifest order plus both drivers. Capture fresh reports
and terminal statuses. Independent `--coqchk -silent -o` uses the same mappings
and root `SqLitC.jet_secp_scalar_square_local`. Process bounds: 120 seconds per
compile, 900 for the whole-dependency kernel. Stale `.vo` files are not evidence
for edited sources.

See `CONTINUATION.md` for normal integration/main reconciliation. Signed atomic
local commits only; never push. Keep the complete all-533 goal active.
