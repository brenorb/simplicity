# Nonce hash: canonical stream and original C shape

This packet prepares the implementation-to-specification proof for
`simplicity_nonce_hash`; **the whole jet remains unproved**.

`Spec.v.source` ports the literal `Programs.Elements.nonceHash` program,
retaining its algebra-parametric construction and its order of operations:
`ctx8Add1` for the prefix, then `ctx8Addn vector32` for a present payload. It
proves its option semantics equals the existing context byte-list model:

- absent nonce: `00`;
- explicit nonce: `01` followed by its 32 bytes;
- confidential nonce: `02` or `03` according to parity, followed by 32 bytes.

The 259-bit optional-nonce encoding includes a padding bit in the explicit
case. The proved encoding matches the C `forwardBits(1)` there. Input context
plus nonce occupies 1089 bits. Word256 payloads are unrestricted; no field or
curve-membership premise is added.

`Shape.v.source` checks the exact generated C statement tree, including the
three distinct tag-reading temporaries, explicit padding skip, byte calls,
context reader/writer and return. It proves the actual four-local function
entry and free-list layout. It does not yet derive the execution of the
nonce branches or compose the complete function call.

`SOURCE-REVIEW.json` preserves the manually compared Haskell program, catalog
binding/type, sum/confidential/point type aliases, selectors and C function,
alongside the exact reviewed Coq source digests. Its drift check supplements
kernel checking; it is not a formal translation of Haskell.

There are seventeen closed results and twenty definitions. `verify.py`
freshly compiles both modules, prints complete contracts/definitions and
assumptions, and binds all 111 loaded project imports to the forced-source
entropy basis. Recursive checking has its own receipt; only `CHECKED.json`
records success. No production target, normal registration or accepted
coverage changes.

Next: derive the actual prefix reads/skip and SHA byte updates from initial
represented input and live context, preserving locals and global loads.
Reuse the existing context reader/writer and invalid-context/overflow cases;
the final public contract must discharge every intermediate call, store and
free premise. The Coq proof-engineering skill guided this split between
canonical stream, exact AST, execution and full composition.
