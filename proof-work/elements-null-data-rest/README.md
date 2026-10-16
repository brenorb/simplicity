# Both reads, complete null-data output and actual return

Private tree: `/private/tmp/jet-null-data-first-read.Z3fuaZN8`.
The new `C.jet_elements_null_data_rest` source is archived under `source/`.
Inherited sources equal the checked `../elements-null-data-guard-compose/`
tree byte for byte. Main418 semantic inputs and original staging are unchanged.

## Proof progress

`exec_elements_null_data_rest` executes the actual first read32(&src), assigns
i, performs the complete261-bit output/conditional second-read block, and
executes the real `return 1`. Its source equality identifies exactly the
function body following the by-value source assignment, with the actual
statement association rather than an invented substitute body.

All memory/representation premises concern the initial memory. Three shared
lemmas transport the output representation and selected opcode representation
through a private source-cursor update and lift the final private output effect
back across that update. The proof establishes the second-read frame fields
from the first reader's actual cursor result; it does not assume that header
already contains the advanced cursor in the initial memory.

Only a successful outer guard requires the second input word, opcode-count
path, selected opcode and conditional hash array. When needed, those initial
facts are preserved through the first read and the previous batch proves their
preservation across the first output tag. Word-range input/output separation
still allows shared data allocations and word-boundary crossings. The first
reader's exact unsigned result fixes i to the logical Word32 value, not merely
a lossy decoding of an arbitrary64-bit result.

## Remaining lifecycle and acceptance work

The theorem stops before function entry/source copying/freeing, not before a
missing branch of the output block. The final effect intentionally excludes
the private source-copy block. Reuse `elements_wrapper_layout` with
`elements_null_data_rest` (not `elements_wrapper_layout_simple` with an
incorrectly reassociated body): the rest is
`first_read; (guard_block; return1)`. The generic wrapper already proves actual
entry,16-byte allocation, source copy and free, and removes the private-block
exception from public framing.

To construct that middle proof, derive source fields with
`frame_copy_fields_at`; derive writable local cursor and fresh inequalities
from allocation/storebytes; transport the initial input/environment loads
through allocation/copy; and derive selected-opcode freshness from its old
code load. Do not introduce an assumed middle execution or post-copy desired
output. A generic full-footprint selected predicate should keep physical
initial representations independent of the fresh block, deriving its
inequality at allocation time.

Then connect the C-memory environment to the logical output/script lookup of
`elements_output_null_datum_guard_sem`, perform canonical Haskell/port source
fidelity review, and apply normal admission. The broader documented API's
overlap question remains open (`../null-data-overlap-probe/README.md`); no
unrestricted overlapping-frame theorem is claimed. The target is the same
pinned assertion-disabled Elements program, not all build configurations.

In particular, the existing `application_jet_local_spec_sep` separates the
environment footprint from output writes but does not itself separate unread
input data from output. Its domain is therefore not interchangeable with this
rest theorem's domain. Do not register a separated-input result under that
broader existing contract or hide the extra requirement inside an environment
predicate. A public evaluator-valid contract must expose/derive the actual Bit
Machine input separation; any broader header-domain result needs the overlap
question resolved explicitly. Wrapper lifecycle composition can proceed without
changing either C or the canonical primitive while this distinction stays open.

This adds **zero registered whole jets**. Main coverage remains418/533 and the
every-jet goal remains unfinished. Nothing here claims clean-HEAD reproduction.

## Verification

The complete new module compiled in the pinned Coq8.17.1 / CompCert3.14
environment. Fresh checker55984 exited0 after explicitly recompiling it,
printing all5 result types and2 definitions without elision, checking AST
regeneration, and recursively kernel-checking the dependency chain.
Independent evidence review19803 exited0 with35 rejected proof/evidence
corruptions. A separate terminal postcheck revalidates the receipt/log/tool
hashes, source/object identities and unchanged main inputs before commit.

The expected scope is one closed source equality, three shared preservation/
effect results using the four inherited classical/extensionality assumptions,
and one execution theorem using the six inherited Coq/CompCert assumptions.
No new assumption, admission or unchecked operation is used.

```sh
python3 -B proof-work/elements-null-data-rest/review.py /private/tmp/jet-null-data-first-read.Z3fuaZN8
```

The new completed module compiled on its first development run. Checker89762
then stopped before recording a launch because a mechanical rename produced an
incorrect execution-declaration key. Corrected checker55984 reruns the fresh
compilation and reports; no proof source changed for that tooling correction.
The two checked base batches retain their separate evidence and commits.
