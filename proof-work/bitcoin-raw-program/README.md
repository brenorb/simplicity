# Raw interpretation of complete Bitcoin Simplicity programs

Private tree: `/private/tmp/jet-bitcoin-raw-program.9b5hGOH3`.
Immutable base: the completed, independently reviewed tapleaf tree
`/private/tmp/jet-bitcoin-tapleaf-literal.7kPleO0v`.
Only two new proof sources are added; both exact sources are archived here.
No inherited source, public registry, main proof input or original stage is
changed. No live audit object cache is copied.

The compile/report phase completed with exit zero (handle13549): all four
reused C execution modules and both new modules compiled freshly, and all
23 results / four definitions were reported completely. All16 concrete
whole-C endpoints retain exactly the six inherited execution assumptions.
`RUN.json` records compilation, not recursive kernel success or admission.
Two results are closed; the four pure algebra/program-relation results use
the inherited dependent functional-extensionality principle through the
Reader algebra. They are not claimed axiom-free. No new assumed declaration
or allowlist change is introduced.

## Shared proof, then complete C endpoints

`raw_fullalg` interprets the existing Bitcoin primitive signature over raw
transaction/taproot data. Base primitives read `raw_base`; the extended
primitives use `raw_ext_sem`, which computes script/annex/scriptSig hashes
from their bytes. It introduces no primitive constructor or namespace.

`bitcoin_program_raw_projection` proves the same meaning for **every**
parametric program under that algebra and the existing cached-environment
projection. The proof constructs a relation for all nine Core combinators,
both assertions and failure, and every primitive. The projection's path bound
stays explicit, as in the existing `raw_env_rep` contract.

`application_raw_program_local_spec_sep` then transports an existing complete
original-C theorem to that program's raw interpretation, retaining all
execution/output/cursor/prefix/load guarantees. Its use is not a mathematical
replacement for the specification: the final targets are the same Simplicity
programs, evaluated with raw primitive semantics. The cached C fields in the
representation are thereby tied to raw data, not arbitrary independent hashes.

The sixteen concrete endpoints discharge the generic helper's execution and
parametricity premises with existing verified proofs. They cover:

- The seven word/hash stream getters: output values/scripts, input values/
  scripts/sequences/scriptSigs, and tappath.
- The reviewed literal tapleaf program, with its computed ASCII tag prefix.
- Outputs, input UTXOs, tap environment, input outpoints, input annexes, inputs,
  transaction and sig-all composite hashes.

Their final statements have no extra execution/desired-output premise. They
retain the existing represented-memory/frame separation premises and the
tap-path bound. This does not establish all real C environment-constructor
caches or eliminate the caller's representation obligation.

## Verification phases and continuation

The completed compile command was:

```sh
python3 -B proof-work/bitcoin-raw-program/check.py compile /private/tmp/jet-bitcoin-raw-program.9b5hGOH3
```

The once-only recursive kernel phase was launched **after** guarded main420
integration, and is now running under handle58669 in parallel with the
separate actual-main420 audit (handle27494):

```sh
python3 -B proof-work/bitcoin-raw-program/check.py kernel /private/tmp/jet-bitcoin-raw-program.9b5hGOH3
```

The phases separately bind unchanged main inputs and the original stage;
authorized guarded main integration may occur **between** them. The exact
private sources and all fresh object hashes must remain identical across the
phases. Kernel mode records its launch before running the Bitcoin AST check
and recursive kernel check. Poll handle58669; never restart from a
launch file or observation timeout. Only actual terminal success writes
`CHECKED.json`.

Then independently review the proof evidence, raw primitive projection, exact
whole-C contracts and the canonical Haskell stream/composite programs before
normal registration. The prior tapleaf source review already checks the
selected SHA helpers and literal word/hash conversions, but does not itself
review the new stream/composite dispatches and loop bodies. Preserve that
distinction. No new coverage, full acceptance or all-caller result is claimed.
