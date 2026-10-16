# Actual second read plus opcode-index branch

Private tree: `/private/tmp/jet-null-data-read-index.jkbo196s`.
Semantic fingerprint:
`1f78837df43dc5c00d103485873d981bd1e765f99fcbba9379d1230c4d63d69f`.
The new source is archived under `source/`. All inherited source bytes equal
the completed `../elements-current-reader/` tree. No main418 semantic input
or original staging changed; no live audit objects were copied.

## Formal progress

`exec_elements_null_data_read_index_block` executes the complete actual true
arm after the outer output guard: the second `simplicity_read32(&src)`, its
assignment to j, and the checked260-bit opcode-index/payload block. The returned
unsigned integer is proved equal to the logical Word32 input; count/path/hash
relations and the output frame are transported across the real local-cursor
mutation before invoking the index proof. No desired execution, intermediate
representation or output is assumed.

Its postcondition is deliberately honest about private memory. The source
cursor has changed, so the entire composition cannot satisfy an unqualified
`write_effect` that pretends every unrelated block is untouched.
`write_effect_private` retains output cells, prefix, cursor, permissions, valid
blocks and all public load framing, excluding the source-copy block until its
actual wrapper free. The theorem also retains the intermediate read-memory
witness, its private-only load changes and the full payload write effect.

`write_effect_private_interleaved` composes a real tag write, a private-cursor
step and a real payload write into the same honest private effect. It preserves
the first tag and earlier output prefix and composes public framing; it is
ready to combine the outer guard with the read/index branch. This internal
effect algebra is not an assumed execution premise of a whole-jet theorem.

Selected environment blocks must be distinct from the fresh local source
block. Two new lemmas derive those conditions from the actual `Mem.alloc m 0
16 = (ma,bl)` and the initial count/selected relations, using their real loads
to establish old valid blocks. They do not assume freshness without allocation.
The wrapper still needs to transport these initial relations through its
allocation/copy/read/guard sequence. Missing indices retain the earlier
conditional-pointer discipline: no selected opcode block is required when
lookup is absent.

A closed equality identifies the entire read/index arm as the actual generated
C subtree, not a substitute body. This batch adds no whole-function endpoint,
normal registration, canonical source gate or coverage entry.

## Verification

Fresh checker45303 exited0: the new module explicitly recompiled, all8 result
types and4 definitions were printed without elision, Elements AST regeneration
matched and recursive `coqchk` accepted the module and its dependency chain.
One source equality is closed; six preservation/freshness/effect results use
the four inherited classical/extensionality assumptions; one execution result
uses the six inherited Coq/CompCert assumptions. No new assumption, admission
or unchecked kernel operation was introduced. `CHECKED.json` binds the fresh
source/object, tools and terminal commands/logs.

Independent evidence review76275 exited0 and rejected35 deliberate proof,
assumption, type, log, source and kernel-scope corruptions. Its terminal evidence
is `EVIDENCE-REVIEW.json`; a separate postcheck revalidates the receipt, tool and
log identities against the current private tree and unchanged main inputs.
Recheck:

```sh
python3 -B proof-work/elements-null-data-read-index/review.py /private/tmp/jet-null-data-read-index.jkbo196s
```

Development corrections were importing the actual cell predicate definition
and exposing the writable frame's cursor bound before arithmetic in the
interleaving lemma. No theorem domain or implementation changed.

## Continue to the whole function

Use the initial full261-bit environment/input footprint to preserve both the
unread j word and selected environment relations across the first output tag.
Do not use only the later260-bit payload footprint: at a word boundary the
earlier tag may touch a different word. The shared range proof in
`C.jet_read_after_write` derives adequate unread-input separation from the
existing formal Bit Machine invariant, allowing read/write data in one block.

Compose the guard with this actual read/index arm via the new interleaving
lemma; compose the false branch's real `1 + 1 + 2 + 256` padding as well. Add
the first read, complete261-bit primitive encoding, function entry/source-copy
and actual free. That free must discharge the private-block framing exception,
not leave it in the final public theorem. Canonical parsed-script/hash caller
construction and independent Haskell/port source/admission review remain.

## API overlap boundary: do not hide it with a stronger contract

A separate native probe now reproduces different tags with overlapping input/
output buffers; see `../null-data-overlap-probe/README.md` for exact controls,
configuration and limits. `jets.h` does not explicitly list non-overlap, while
the evaluator and `bm_separated` use disjoint word slices. The probe is not a
formal counterexample and does not use the full environment builders; it is
not a failure demonstrated on valid evaluator layouts. Nevertheless, keep the
broader documented-API aliasing question open rather than claim an unrestricted
header-domain theorem from only the separated-layout result. No C, primitive
or header was changed to resolve that question in this batch.

Actual-main418 acceptance remains the live handle6155. Preserve its semantic
inputs. The every-jet goal remains active/incomplete; this batch adds0 whole-
jet coverage and claims no clean-HEAD reproduction.
