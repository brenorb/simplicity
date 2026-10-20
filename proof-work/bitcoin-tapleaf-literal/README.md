# Bitcoin tapleaf_hash: literal tagged-hash program

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

No normal registration, full acceptance, actual-main coverage increment or
C environment-constructor result is claimed here.
The all-jet goal remains incomplete. Keep main418 frozen while the combined420
audit finishes, then use its guarded installer and actual-main audit; do not
install this unregistered proof as an unrelated part of that reviewed delta.
