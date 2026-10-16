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
Bitcoin AST matched. Recursive kernel checking is running under the original
checker handle66822; `RUN.json` is not terminal kernel-success evidence.

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

Poll checker66822 rather than restarting it. It runs:

```sh
python3 -B proof-work/bitcoin-tapleaf-literal/check.py /private/tmp/jet-bitcoin-tapleaf-literal.7kPleO0v
```

The script refuses a second launch once `RUN.json` exists. After real terminal
success, `CHECKED.json` binds the fresh sources/objects, all commands/logs,
full types/definitions, exact per-result assumptions, kernel check, unchanged
main/index and the accepted418 base. Independently review that evidence and
the selected canonical Haskell/Coq program, primitives, tag/decoder and SHA
helper definitions before normal delta preparation. In particular, source
correspondence is not a formal Haskell runtime/crypto-library equivalence.

No source-review gate, normal registration, full acceptance, actual-main
coverage increment or C environment-constructor result is claimed here.
The all-jet goal remains incomplete. Keep main418 frozen while the combined420
audit finishes, then use its guarded installer and actual-main audit; do not
install this unregistered proof as an unrelated part of that reviewed delta.
