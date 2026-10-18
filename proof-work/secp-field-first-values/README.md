# First original field-multiplier checkpoint: actual integer values

`exec_first_integer_atomic` executes the first 32 statement heads of the
original C `fe_mul_inner`, through its first `d >>= 52`. It retains the
current-memory `c`/`d` loads, live `t3`, atomic cell/temp representations and
outside-memory framing established by `../secp-field-checkpoint`, and proves:

- `c` has value `p8 / 2^64` and is below `2^40`.
- `d` has value `(p3 + R * (p8 mod 2^64)) / 2^52` and is below `2^63`.
- `t3` is the complementary remainder modulo `2^52`.
- The intermediate 128-bit additions do not overflow under the stated bounds;
  those guards are derived, not additional premises.

Here `p3` and `p8` are the actual input-limb product sums and
`R = 68719492368`. The input condition is the implementation's 56-bit bound
for the lower four limbs of each operand and 52-bit bound for each top limb.
The eventual public proof must establish this condition from its real reader.
This packet does not discharge that caller obligation, the remaining original
statement slices, the final modular product, or public jet equivalence.
Nothing is registered and coverage does not increase.

The fifteen results comprise fourteen closed arithmetic observations and one
execution theorem with exactly the six inherited Coq/CompCert dependencies.
The source is freshly compiled against the independent 95-source audit tree
`/private/tmp/jet-field-checkpoint-audit.Zeze9g`, with namespace `FieldFirst`
in its separate `arith/` directory. The parent `RUN.json` binds its successful
forced-source build; no stale main object is counted as evidence. The pure
parent `Columns` module is not a dependency of this first-slice result.

`RUN.json` records successful compilation, full contracts and assumptions;
only `CHECKED.json` additionally records a completed recursive kernel check.
Poll a running original handle rather than restarting it.

```sh
python3 -B proof-work/secp-field-first-values/verify.py kernel \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
```

Next slice: original statement heads 32 through 49, starting from these
proved machine values and atomic memory/temp representations. Derive the
next entry facts, do not assume a fresh layout or the next desired output.
Keep the live cached inputs, pointers, `M`, `R` and `t3` when constructing
its temporary relation. Continue toward the complete fixed C-to-literal-
Simplicity theorem, not only the unbounded algorithm's conservation identity.
