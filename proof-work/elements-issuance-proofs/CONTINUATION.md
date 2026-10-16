# Continue the issuance range-proof endpoint

The original C-to-program proof freshly compiles; full reports are in
`RUN.json`. Canonical-source review passed43 corruptions in
`../elements-issuance-proofs-source/`. Source/private fingerprint:
`33ffafe0efa1a2773f95474fc1a7800c426d878f9346abbb32d57ba8a2c58a51`.

The once-only recursive kernel/AST controller is live under handle8870:

```sh
python3 -B proof-work/elements-issuance-proofs/kernel.py /private/tmp/jet-elements-issuance-proofs.OurYz6Pe
```

Poll that existing handle. The kernel is CPU-active and silent; do not restart
because `CHECKED.json` is absent or observation times out. Do not change this
private source/object tree while it runs.

The added `review.py` and `test-review.py` are review tooling, not completed
evidence. Their syntax and source/report phases passed on real current
evidence. After the actual kernel controller succeeds, run:

```sh
python3 -B proof-work/elements-issuance-proofs/review.py finish /private/tmp/jet-elements-issuance-proofs.OurYz6Pe
```

That command must verify the real kernel receipt/log/context, all11 results
and seven definitions, complete commands/source/object reports, the43 source
mutations, exact inherited outpoints proof and historical main bytes, then
run independent evidence mutations. Record its actual exit and only then
claim independent evidence review. It must preserve the original staged patch.

The separate `inputs_hash` package is already recursively kernel/source/
evidence-checked in `../elements-inputs/`, committed as290af8b4. Neither new
endpoint is normally registered. A later two-jet449 candidate can reuse these
exact completed sources over447 once both are fully reviewed; do not copy
objects from the live447 audit or claim full449 acceptance from older checks.

The real full443 audit passed (receipt in `../elements-stream-admission/`).
The full447 audit is live under handle50964 with the tested controller in
`../elements-context-admission/accept.py`. Keep its sources, review evidence,
controllers and main420 immutable through its terminal postchecks. Main420
fingerprint remains `c30bd6ac82c17410b9315a9e06d8b026294434a96180612bd717e7e4c8a64f21`;
the staged patch remains `f2083389e06d3a5aed12c83d0aae554895eab94eef8e107c5d445f9268d86bbe`.

Coverage and the every-jet goal remain incomplete; cache-construction and
formal host-library boundaries are not discharged by these getter theorems.
