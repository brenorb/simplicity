# Canonical Elements two-primitive outpoint-loop source review

The inherited annexes/stream guards cover the canonical SigHash library body,
marker/SHA program, generic element loop, primitive port and word/hash/getter
contracts. This extension follows `InputOutpointsHash` through its selector,
two optional primitive lookups and early-exit routing, the Elements absorber
(pegin marker/hash, outpoint hash,32-bit index), raw logical list, generic-body
bridge, and original C getter to the entire separated endpoint contract.

Tests reject swapped primitives, lost option layers/markers, reversed stop
branches, changed word widths or signed indices, wrong libraries/SHA lengths,
wrong C fields, the initial incorrect312 offset instead of216, and weakened
or vacuous final contracts. The loop/body equivalence is a formal Coq result;
this tool's role is canonical-source correspondence, not proving its kernel
term or checking the actual caller's cached-field construction.

Host Haskell/SHA library verification, recursive kernel evidence, independent
proof-evidence review and normal registration/acceptance remain separate.
No accepted coverage addition or every-jet completion is claimed here.
