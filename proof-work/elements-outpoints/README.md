# Elements input_outpoints_hash: literal two-primitive loop and original C

Private tree: `/private/tmp/jet-elements-outpoints.W5XLYp4T`.
Seed: the completed annexes proof tree
`/private/tmp/jet-elements-annex.sihNn4TS`; no live audit objects were copied.
Main Coq inputs and the user's staged patch remain unchanged.

`source/jet_elements_outpoints_hash_program.v.source` proves the actual
`f_simplicity_input_outpoints_hash` getter against the literal Elements program.
It retains the two separate primitive lookups and early exits of the canonical
loop. A formal equality relates that body to the existing generic element-loop
body, so the previously verified prefix, counter traversal, SHA absorption and
finalization proofs are reused without enumerating the32-bit counter space.

The element absorber is the literal Elements outpoint helper: absorb the
optional pegin using the zero/one marker, then the outpoint hash and32-bit index.
Its option semantics and maximum69-byte length are proved. Both pegin cases
and both loop exits are covered; no extra execution/output premise is added.

Fresh compilation and complete declaration/assumption reporting succeeded:

```sh
python3 -B proof-work/elements-outpoints/check.py /private/tmp/jet-elements-outpoints.W5XLYp4T
```

`RUN.json` and exact logs bind13 results and eight definitions: seven results
are closed, five use inherited functional extensionality, and the public C
endpoint has exactly the six inherited assumptions. Source fingerprint:
`85ac036384babe0b3b2a734e13378fb9880526eb062519dd89f44ef4427600e5`.

The explicit separated cache/frame relation places the computed raw outpoint
hash at transaction offset216. The AST layout proof caught and corrected an
initial proof-side312 assumption (that is the different inputUTXOsHash field);
the checked theorem uses216. This was not a C/specification mismatch. Actual
caller cache construction and host-library verification are not claimed.

The once-only recursive-kernel/Elements-AST phase completed with exit zero
under handle41935:

```sh
python3 -B proof-work/elements-outpoints/kernel.py /private/tmp/jet-elements-outpoints.W5XLYp4T
```

`CHECKED.json`, `KERNEL-RUN.json`, `ast.log` and `kernel.log` bind the actual
recursive kernel and Elements AST-regeneration success. Canonical-source
review and54 read-only mutation fixtures passed, recorded separately in
`../elements-outpoints-source/`. Independent evidence review also completed
with exit zero, including52 proof/kernel/command/source/report/object/
dependency corruptions. `EVIDENCE-REVIEW.json` and `evidence-tests.log` bind it.

`historical-annex-review.py` preserves the frozen annexes reviewer/receipt and
all its checks, replacing only its live-main420 equality with the exact
historical accepted map and actual immutable private bytes. It agreed with
the original reviewer on real complete evidence. The new evidence tests also
confirm historical review works when live-main-map access raises an error;
no fictitious source map or filesystem view is supplied. This avoids making
an old proof checkpoint depend on a successor's current main state.

Normal registration/admission remains. This is not accepted extra coverage,
full normal acceptance or completion of the every-jet goal. Main420 and the
isolated443 full audit stay frozen and separate; neither's inputs or objects
were changed by this work.
