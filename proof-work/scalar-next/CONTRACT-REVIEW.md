# Scalar support contract review

Compiler generation 26431 exited 0 for standard then depth-10000 reports.
All 86 actual helper types and 64 actual definitions are accounted for; both
diagnostic streams are empty. The deep report is 94938 lines and contains no
ellipsis. Every helper source matches its freshly compiled/kernel-checked hash.
CONTRACT-REVIEW.json records both actual output hashes and all supplement names.

81 types and 46 definitions match exactly modulo whitespace. Five types and
18 definitions require the deep supplement. These include unary length 32,
64/256-bit numeral constructors and computed execution trees. Retained fragment
comparison anchors both ends; repeated closing parentheses in binary numerals
must not be confused with an earlier identical suffix. Fixtures exercise this
case and reject changed prefixes, suffixes, order and specification names.
This comparison is a diagnostic, not proof of omitted-term equality. Actual
source and independent kernel evidence are essential, not replaced by comments.

The actual code-support chain preserves its original contracts:

- Scalar overflow reads four represented 64-bit limbs; the new theorem derives
  its actual flag as the comparison with the group-order literal for arbitrary
  int64 values. Unsigned bounds are discharged, not added as public premises.
- Scalar-zero helper execution uses a represented owned 32-byte region. Its
  canonical bridge still requires a caller-derived value correspondence: that
  is an outstanding reader obligation, not a completed public theorem.
- Scalar-get helpers execute the real byte encoding and expose byte-region
  representation and outside-footprint load preservation. A public writer still
  must derive those representations and connect writes to the encoded term.
- Shift64 is a proved specialization of the real original u128 helper. The
  executable oracle is accepted only for count 64, base offset zero and actual
  16-byte ownership. Its correctness derives both stores and the real call;
  scalar reduction uses that literal count. No arbitrary-shift claim is made.
- Scalar reduce/set execute the original functions, including the NULL overflow
  branch, real entry and local frees. The set proof recombines an exact actual
  AST prefix/suffix. Their output integer/mod-group correspondence remains open;
  symbolic execution alone is not the canonical public specification bridge.
- The historical canonical scalar ports remain support pending fresh literal
  source/parametricity checks. In particular scalar_is_zero's raw group-order
  equality branch must be preserved; it cannot be silently replaced by numeric
  zero or a new input-domain restriction in the eventual public result.

Reproduce read-only checks:

```sh
python3 proof-work/scalar-next/review-assumptions.py --work /tmp/jet-scalar-reverify.8hswEF
python3 proof-work/scalar-next/review-contracts.py --work /tmp/jet-scalar-reverify.8hswEF
python3 proof-work/scalar-next/test-review-contracts.py
```

Independent kernel 44992 exited 0; per-result generation 8576 exited 0 and
reviews all 86 sets (57 closed, six inherited execution assumptions only).
No new assumed call/output/free, library model or unsafe kernel option is
introduced. Imported context's fifteen axioms are separately recorded in the
kernel receipt; they are not the union of actual per-result dependencies.
No public scalar jet, accepted coverage or every-jet completion is claimed.
