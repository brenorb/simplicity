# Original field multiplier: through the first output store

`exec_original_third_integer_atomic` executes the first 68 original statement
heads of `f_secp256k1_fe_mul_inner`, through its first `r[0]` store and the
following 52-bit shift. Source-splitting equalities are checked against the
unchanged Clight body, with the original input/output alias `r = a`.

The next slice's memory and live temporary entry are derived from the actual
second checkpoint, not new caller premises. Its current output load is proved
in the post-store memory. The original cached `a0` is preserved even though
`a[0]` has been overwritten. Atomic cell/temp representations and framing
outside the original footprint are retained for subsequent slices.

Under the explicit implementation limb bounds, the accumulated `d` and `c`
are exact unbounded integer sums: all intermediate additions fit in 128 bits.
The shifted `d` is below `2^63`, shifted `c` below `2^61`, `u0` below `2^56`,
and stored `r[0]` below `2^52`. Their exact values and the low-nibble packing
are derived from the earlier checkpoints. The reusable `shl4_or_unsigned`
lemma proves the disjoint shifted bit fields add without overflow.

This remains a partial helper proof, not a complete C-jet-to-Simplicity
equivalence theorem. Later multiplication stages, final field-product bridge,
original function entry and jet reader/writer/lifecycle composition remain
open; the reader must still establish the implementation limb bounds.
No production C, original specification, API, generation setting, main proof
source or registry is changed. Coverage added: zero.

## Evidence

The six sources have 49 results and 39 definitions. The exact expected profile
is 46 closed results and three execution theorems with only the six inherited
Coq/CompCert dependencies. `RUN.json` records fresh compilation and full
type/definition/assumption reports. `CHECKED.json` additionally records
completed recursive kernel verification. A launch file is not success.

Audit tree: `/private/tmp/jet-field-checkpoint-audit.Zeze9g`, with these six
sources in `third/` under `FieldThird`. The parent receipt binds the 95 local
imports, all previously forcibly rebuilt and checked, plus 19 checked extension
modules. Every loaded module's source/object provenance is checked.

```sh
python3 -B proof-work/secp-field-third/verify.py compile \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
python3 -B proof-work/secp-field-third/verify.py kernel \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
```

Next: carry the updated region 0 and original cached inputs into the slice
ending with `r[1]`. Do not reconstruct an initial input array or assume that
its old `a[0]` load still holds after this first store. The returned atomic
state contains the updated region and all live cached temporary values.
