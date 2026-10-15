# Original C lbtc_asset to canonical Simplicity scribe

This is one **unregistered** whole-jet equivalence, not another specification-
only lemma. Main was 386/533 at preparation and has since advanced to 399/533
through guarded installation. The separately reviewed 401 candidate is
unchanged; this proof is not silently folded into either existing candidate.

Private tree: `/private/tmp/jet-elements-lbtc-asset.dAZaZ0`. Its compiler objects
were copied only from the completed normal tap-getter tree (`c86dfb59...`), not
from a running audit. All inherited Coq/C/Haskell source/metadata files retain
their bytes; three new modules are archived under `source/`.
Checked input:
`9fc56dff734e3aec3b79111fcf521054abb2f35451ed0bda7ca6644c327af644`.

## The actual implementation and target

`elements_lbtc_asset_local_spec` proves the generated
`f_simplicity_lbtc_asset` call in `elements_ge` returns true and writes the
canonical constant, preserving the output prefix, updating the destination
cursor, and framing permitted memory changes. It retains arbitrary initial
output bits and general valid frame offsets/cursors/crossings.

There is no cached-value, initialized-global, helper-execution or desired-output
premise. The environment footprint is empty and the logical environment is
unused, just as in C. The proof derives both local allocations, the actual
by-value source copy, all eight uint32 stores, the verified `writeHash` call,
return conversion, and freeing both locals.

The target is the literal canonical core program selected by
`specificationIssuance LbtcAsset = Prog.lbtcAsset`, not the alternate Haskell
jet implementation or an informal assertion about the correct asset ID.
`Programs.Elements.mkLib` defines this program as `scribe` of `toWord256 /
integerHash256 / review (over le256)` at its literal integer. The source guard
checks that exact dispatch, library alias, expression and constant. No proof of
the mathematical meaning or genesis derivation of the asset ID is required or
claimed.

The formal byte model reads the integer little-endian, and the proved
`lbtc_asset_review_le_bytes` identifies it with reversal of the native four-
Word64 big-endian serialization. `lbtc_asset_spec_cells` checks the actual eight
C words against the scribe's bits. These are bounded closed computations, never
symbolic reduction of an open memory goal.

## Reusable structure

`exec_u32_local_prefix` proves direct uint32 initialization with a continuation,
read-back values, preservation of loads outside the initialized range,
permissions and valid blocks. It is independent of the Elements global
environment and accepts a proved local-address evaluation lemma, not an
execution/output assumption. This factors the initialization pattern for future
jets with local constant arrays. The concrete module separately proves the
actual struct/array addresses, function entry and writer-call boundary.

The native word serialization definitions and `byte_unsigned_list_inj` also
support later byte/limb bridges. Byte equality is proved through unsigned values
and `Byte.repr_unsigned`; it does not assume proof-field convertibility after
computation or add proof-irrelevance axioms.

## Verification state

All three modules compile with the pinned normal Coq 8.17.1 / OCaml 4.14.4
compiler. The full private checker **75436 terminated with exit 0**: fresh
compilation, complete reports for 13 results and 12 definitions, assumptions,
source guard, 22 source corruptions, direct Elements AST regeneration and
recursive `coqchk` all passed. `PREPARATION.json` and full logs bind those
checks. Four constant/byte/parametricity results are closed; the C endpoint
retains the six inherited Coq/CompCert assumptions, with no libc premise.

The independent review and all **23 evidence-corruption fixtures passed**;
harness **62819 terminated with exit 0**. `EVIDENCE-REVIEW.json` binds those
terminal commands, tools, complete logs and the original preparation/review
receipts. Historical commands:

```sh
# Checker already completed; do not overwrite its recorded objects/receipts.
ulimit -s 65520
python3 -B proof-work/elements-lbtc-asset/check.py /private/tmp/jet-elements-lbtc-asset.dAZaZ0
python3 -B proof-work/elements-lbtc-asset/review.py
python3 -B proof-work/elements-lbtc-asset/test-review.py
```

The terminal evidence and all full type/definition/assumption/AST/kernel/source/
negative logs are archived here. Normal registration,
full normal acceptance, guarded source-only installation and distinct actual-
main acceptance remain necessary. Reuse the existing admission machinery and
preserve the complete older snapshots/dependency sets; do not count a helper or
this private receipt as an extra registered jet.

The actual-main 386 audit **92335** and isolated 399 audit **61966 both passed**.
This proof's independent preservation check was completed at the original main
386 checkpoint, before successor installation; its context is historical once
main advances. The private source/object/log fingerprints remain authoritative
for the proof itself. The 399 installer and proposed 401 candidate are already
prepared; coordinate this next jet with that existing chain without restarting
completed audits or copying objects from live audits. The actual-main 399 and
isolated 401 audits have since been launched as **90475** and **55506**; keep
their source inputs frozen. This lbtc proof remains separate and unregistered.

The source guard is not a formal compiler or host lens/serialization proof.
LP64/RECKLESS and the six inherited assumptions remain explicit. There are no
admissions, new assumptions, unchecked casts or skipped kernel checks. The full
every-jet goal, including all other pending jets and shared obligations, remains
unfinished.
