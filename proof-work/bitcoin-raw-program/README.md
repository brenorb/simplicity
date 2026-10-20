# Raw interpretation of complete Bitcoin Simplicity programs

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
