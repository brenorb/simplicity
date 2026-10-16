# Bitcoin tapleaf_hash: literal tagged-hash program

Private tree: `/private/tmp/jet-bitcoin-tapleaf-literal.7kPleO0v`.
Base: completed accepted418 candidate
`/private/tmp/jet-txid-admission.gvp5bmft`, never the live420 object cache.
Main, its original staged patch, and the two normal candidate trees are
unchanged. Only one new source is added to this private tree; its exact source
is archived under `source/`.

The final new module and both reused tapleaf specification/execution modules
compiled freshly. Four complete results and six definitions were reported
without truncation. Three bridges are closed, including computation of the
tagged midstate from the literal seven ASCII bytes of `"TapLeaf"`. The whole-C
endpoint has precisely the six inherited execution assumptions. The generated
Bitcoin AST matched. Recursive kernel checking and the controller's final
source/index checks passed with exit zero under handle66822. `CHECKED.json`,
`ast.log` and `kernel.log` bind the successful terminal; `RUN.json` alone is
not terminal evidence. No normal admission or coverage increase is claimed.

## What the new theorem proves

`bitcoin_tapleaf_hash_literal_local_spec` executes the actual original
`simplicity_bitcoin_tapleaf_hash` function and establishes the output of the
literal Simplicity tapleafHash combinator program, with the existing complete
cursor/output/prefix/load framing contract. It invokes the existing whole-C
proof rather than assuming execution or a desired final memory.

The program uses the canonical tag construction (SHA-256 of the ASCII tag,
then compression of that digest repeated twice), the existing checked
four-limb digest-to-word decoder, and literal `toWord8 32`. Its complete
algebra-polymorphic program equality is proved before specializing to the
primitive option semantics. The bytes/tag-midstate bridges are closed
computations; no symbolic memory or open SHA goal is normalized wholesale.

The unchanged precondition is `hash_getter_rep tapleaf_hash_of 8 8 176`, plus
the existing environment/output separation and frame premises. It states that
the cached tapleaf field represents the logical tagged hash. This new module
does not prove that the real C environment builder established that cache,
nor does it silently strengthen or remove the original representation.

## Remaining checks and continuation

The completed checker was invoked as:

```sh
python3 -B proof-work/bitcoin-tapleaf-literal/check.py /private/tmp/jet-bitcoin-tapleaf-literal.7kPleO0v
```

The script refuses a second launch once `RUN.json` exists. `CHECKED.json`
binds the fresh sources/objects, all commands/logs,
full types/definitions, exact per-result assumptions, kernel check, unchanged
main/index and the accepted418 base. Independently review that evidence and
the selected canonical Haskell/Coq program, primitives, tag/decoder and SHA
helper definitions before normal delta preparation. In particular, source
correspondence is not a formal Haskell runtime/crypto-library equivalence.

The selected-source guard now passes, including 87 read-only corruptions.
It pins 48 complete typed Coq declarations and seven complete Haskell program/
helper blocks, plus selected routing, primitive, digest/carrier and C clauses.
The independent reviewer completed with exit zero under handle68092. All
three source/evidence commands passed, including 87 selected-source and
35 proof/object/type/assumption/command/scope corruptions. The final
`EVIDENCE-REVIEW.json` binds the successful checks and exact tools/model/logs.
Its historical baseline comparison deliberately validates immutable418 inputs
rather than demanding that a later installed main successor still be418.

No normal registration, full acceptance, actual-main coverage increment or
C environment-constructor result is claimed here.
The all-jet goal remains incomplete. Keep main418 frozen while the combined420
audit finishes, then use its guarded installer and actual-main audit; do not
install this unregistered proof as an unrelated part of that reviewed delta.
