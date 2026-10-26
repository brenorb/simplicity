# Core padding and copy overlap: native evidence

At `d82a21c7`, the original `LEFT_PAD_LOW_`, `LEFT_PAD_HIGH_` and
`LEFT_PAD_HIGH_1_` macros in `C/jets.c:425--473` write before preserving the
input. The original partial-word copy path in `C/frame.c:200--219` clears the
destination before reading aliased source bits. Written individual-frame
preconditions are at `C/jets.h:12--22` and `C/frame.h:201--208`; the individual
frame definitions are at `C/eval.c:100--114`.

The sixteen canonical padding bindings are in
`Haskell/Core/Simplicity/CoreJets.hs:603--622`; the original-input-preserving
expressions are in `Haskell/Core/Simplicity/Programs/Word.hs:128--139`.
`Coq/C/JET_COUNTEREXAMPLES.md` lists exactly one concrete input and the expected
versus observed result for each affected jet, plus the non-jet copy helper.

The reproducer and exact build command are in
[`proof-work/core-overlap-counterexamples`](../../proof-work/core-overlap-counterexamples/README.md).
Against unchanged production C, the 2026-10-26 arm64 clang/ASan/UBSan run with
64-bit UWORDs, PRODUCTION and O2 reproduced all 17 wrong overlap results and
34 correct disjoint controls with exit zero and no sanitizer diagnostic.
This establishes native wrong values for direct calls with overlap. It does
not establish pinned CompCert execution, a whole-public formal refutation,
evaluator reachability, or an exploitable/consensus impact. Sanitizer success
does not prove universal absence of undefined behavior.

The current evaluator's separated word slices exclude these fixtures; no
accepted separated-frame proof is refuted and no coverage row is changed.
No C, API, specification or generated AST correction is made. The former
two-row counterexample report and its first ZIP omitted these native cases;
the corrected report distinguishes native evidence from formal counterexamples.
