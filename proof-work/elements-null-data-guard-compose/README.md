# Outer tag, conditional input read and complete null-data payload

## What is proved

`exec_elements_null_data_guard_block` executes the complete actual generated
261-bit output block of `simplicity_output_null_datum`: output-count check,
short-circuit isNullData load, outer tag, conditional second read32, opcode-count
check, all opcode/push/hash alternatives, and both levels of absent padding.
A closed source equality ties the block to the actual function body.
This is the same pinned assertion-disabled Elements translation unit as its
dependencies, not a new claim covering assertion-enabled build configurations.

The theorem covers both outer outcomes. Its initial read/count/opcode premises
are conditional on the outer test succeeding. Thus the false case needs no
second input read or opcode pointer; the earlier nullable/out-of-range contract
is preserved. `exec_elements_null_data_guard_absent` also exposes that case with
an ordinary full write effect, because it never mutates the source frame.

For the true case, the full initial261-bit footprint protects the unread j
word, parsed-opcode path, count and conditional hash words across the outer
tag. The proof derives the remaining260-bit writable frame and representation
in the actual post-tag memory before executing the checked read/index block.
It does not assume a post-write representation or an execution/output result.
Input and output data need not have distinct blocks: word-range separation
is sufficient, including arbitrary valid cursors and word-boundary crossings.
The previous batch's `C.jet_read_after_write` derives this word separation from
the formal Bit Machine representation and separation invariant.

`elements_output_null_datum_guard_sem` connects the complete encoded value to
the existing canonical `Elements.sem Elements.OutputNullDatum`, given the
logical output/script lookup. The C-memory representation still has to be
connected to that logical lookup by the final environment relation; no parser
or cached-hash construction theorem is claimed here.

## Exact remaining boundary

This is **not yet a whole-function jet theorem or a coverage addition**.
The first input read, function entry, by-value source-frame copy and final free
remain to be composed. The output effect excludes the private source-copy
block because the true branch changes its cursor. The final wrapper must
actually free that block and remove the exception from public framing; the
existing `elements_wrapper_layout_simple` proves that lifecycle for a suitable
middle-block proof and should be reused.

The ready relation reports physical source/environment representation and
separation only. Fresh local/environment block inequalities must eventually
be derived from actual allocation, not left as unexplained caller obligations.
The canonical source/Haskell-port fidelity gate, normal registration and full
acceptance of this jet also remain. Main coverage is still418/533, not419.

The separate native overlapping-buffer diagnostic remains an API-domain
question (`../null-data-overlap-probe/README.md`). These theorems do not assert
arbitrary overlapping-buffer correctness or a production evaluator failure.
No C implementation, header or canonical specification was changed.

## Verification

The complete module compiled with the pinned Coq8.17.1 / CompCert3.14
environment. Fresh checker11143 exited0 after explicitly recompiling it,
printing all9 result types and6 definitions without elision, regenerating the
Elements AST and recursively kernel-checking the dependency chain.

The assumption report identifies three closed results (source equality,
Word32-to-Int64 unsigned bridge and canonical primitive bridge), three results
using four inherited classical/extensionality assumptions, and three execution
results using the six inherited Coq/CompCert assumptions. No new axiom,
admission or unchecked operation was introduced.

Independent evidence review78938 exited0, including35 rejected read-only
proof/evidence corruptions. The separate terminal postcheck revalidates its
receipt/log/tool hashes and actual source/object identities. Recheck:

Development corrections were missing explicit imports, specifying the actual
write cursor/effect before solving existential side conditions, using the
installed integer API's `repr_unsigned` equality, and annotating a boolean
binder before its conditional expression. No theorem was weakened to bypass a
proof obligation. No clean-HEAD reproduction is claimed for the main tree.
