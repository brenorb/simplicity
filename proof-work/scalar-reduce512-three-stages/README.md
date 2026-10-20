# Checked first three original scalar-reduction stages

Six new modules / 30 results / 28 definitions extend the frozen
`scalar-reduce512-two-stages` milestone. Last complete declaration:
`MulC.jet_secp_reduce512_three_stages.exec_reduce512_first_three_stages`.

The root executes the unchanged generated C body prefix through the actual
`_c` assignment, preserving original rho, concrete memory and temp environment.
It proves current-memory loads for all four stored output limbs, actual carry
temp equality, exact third-fold reconstruction, a value below twice the
canonical group order, carry in [0,1], and residue preservation relative to
the checked second fold. It retains representation, temp agreement and
outside framing.

The only root entry assumptions are allocated owned-region representation,
initial parameter-temp agreement and actual local-environment agreement.
The typed third checkpoint, actual p4 range/cast, scratch representation,
all u128 non-overflow guards and phase execution are discharged internally.
The stage helper's explicit p4<=2 arithmetic condition is derived from the
actual preceding execution at composition; it is not a new public premise.

## Source and execution boundaries

`third_stage` extracts the original spine from p4 through c and checks both
the boundary and exact reconstruction. Its compact run completes; the three
shift-oracle log entries are verified, not omitted. The oracle itself has an
existing proof for execution of the original u128_rshift C function at 64.

`third_atomic` connects the actual stored expressions and carry to factored
u128 operations. It preserves unsigned p4 promotion, original multiplication
operand order and real shift writes. The shift oracle writes `XLc Int64.zero`
to the high cell; that is not syntactically the macro's promoted int zero.
A small source-specific shift adapter reuses the proved wide-column bridges.

`third_value` proves the exact arithmetic of every column, derives all fast
guards, reconstructs output-plus-radix*carry, and derives the sharp bounds.
`third_exec` establishes actual execution and reads the output from its
**resulting** memory, using its actual region invariant and source denotation.

`third_checkpoint` establishes lossless p4 representation and range, the
integer split/residue bridge, and one-way temp agreement. Only scratch-local
logical values are forgotten. Initialized input/output regions are retained.
`three_stages` composes these results with the checked first two prefixes.
No assumed execution/output/free fact replaces an implementation obligation.

This is still an internal **body-prefix** theorem, LP64 / RECKLESS on owned
allocations. Final overflow/scalar_reduce execution/value composition, whole
function entry/return/local freeing, public multiply/square lifecycle and
literal canonical Simplicity equivalence remain unfinished. No coverage
entry or full acceptance is added. Main remains 351/533; isolated scalar-add
359/533 still awaits exact main integration and verification.
