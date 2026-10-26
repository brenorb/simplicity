# Native core overlap counterexamples

One input per padding jet and one eight-bit copy-helper input, each with
overlapping storage and two controls: separate arrays, and disjoint word slices
of one array. Exit zero means all expected wrong overlap results and all correct
controls reproduced, not that the implementation is correct. The helper returns
void; its printed success flag comes from the test adapter.

Run from the original repository root on macOS:

```sh
overlap_build=$(mktemp -d /private/tmp/simplicity-core-overlap.XXXXXX)
cc -std=c11 -O2 -g -DPRODUCTION -DUWORD=uint64_t \
  -fsanitize=address,undefined -fno-omit-frame-pointer \
  -ffunction-sections -fdata-sections -I C -I C/include \
  proof-work/core-overlap-counterexamples/probe.c \
  C/frame.c C/jets.c C/sha256.c C/jets-secp256k1.c \
  -Wl,-dead_strip -o "$overlap_build/probe"
ASAN_OPTIONS=detect_leaks=0 UBSAN_OPTIONS=halt_on_error=1 "$overlap_build/probe"
```

The checked run on 2026-10-26 used Apple clang 21.0.0, Darwin arm64, 64-bit
UWORDs, production and O2. It produced 17 wrong overlap results and 34 passing
controls, without sanitizer diagnostics. No fresh eight-configuration run is
claimed. Production C matches revision `d82a21c7`.

This is native evidence, not CompCert execution, a formal refutation, an
evaluator-reachable failure or a consensus/exploit demonstration. The frame
descriptors do not alias the backing data. The original evaluator maintains
separated backing-word slices. No production source, API or specification is
changed and no jet coverage is added.

The concrete results appear individually in
[`JET_COUNTEREXAMPLES.md`](../../Coq/C/JET_COUNTEREXAMPLES.md). The additional
cases were recovered from the user-supplied `simplicity-mismatches.md` report;
its proposed fixes were not applied.
