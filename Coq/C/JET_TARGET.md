# Original implementation target and equivalence criteria

The target is `e3b670103101108faa238df012676ff5d8b77cf9` (Bitcoin Application
merge #324). Its production C and canonical Haskell sources are byte-for-byte
identical to the proof-branch base `ebf1749340f623be7e0e43a1a6b3a7cccf560e2e`.
`jet_source_target.tsv` pins SHA-256 hashes of 231 files from that commit, plus nine reviewed generation
inputs from the proof development.
`check-jet-source-target.py` checks both their contents and their file set.
`C/test.c` is excluded because it is a test harness absent from all four proof
translation units; our cursor-alignment regression tests remain in that harness.

## Target configuration

* Coq 8.17.1; CompCert 3.14; VST 2.14 as pinned in `../jet-deps.sh`.
* Clight target: x86-64/Linux, standard ABI, little endian, LP64. The original
  `UWORD` default is `uint_fast16_t`; the pinned amd64 headers make it 64 bits.
* Genuine glibc headers from `libc6-dev_2.36-9+deb12u14_amd64.deb`, SHA-256
  `0218fc2befcd784c1b0c6292c0a137ce89fad054efaa579ad083bee0f2c01aae`.
* `clightgen-linux.ini.in` supplies `-target x86_64-linux-gnu`, `-nostdinc`, the
  CompCert runtime includes and the glibc sysroot. It undefines `__GNUC__` and
  `__SIZEOF_INT128__`; generation additionally undefines Clang identification
  macros and uses `-std=c11 -normalize -fstruct-passing -DPRODUCTION -IC -IC/include`.
  These are the existing proof configuration, not changes to replace memcpy.
* `jet_translation_unit.c`, `jet_bitcoin_translation_unit.c`,
  `jet_sha_translation_unit.c`, and `jet_secp_translation_unit.c` include actual
  repository implementation files. Their regeneration scripts produce `jets.v`,
  `jets_bitcoin.v`, `jets_sha.v`, and `jets_secp.v`; acceptance compares all four
  with independently regenerated artifacts. The target is this configuration,
  not every compiler, assertion mode, UWORD width or SHA dispatch variant.

## Correction of implementation drift

Commit `b058d5a6` added a C `copyWords` helper and changed `copyBitsHelper` to call
it. Its typed one-word load/store was verified, but the resulting removal of
`memcpy_model` from 92 copy-family theorems was about that modified implementation.
It did not prove the corresponding paths of the original C. That implementation
change has now been reversed without resetting either branch or discarding the
experimental proofs. The one-word and two-word execution proofs again dispatch
the actual external call. `jet_copyWord.v` retains reusable byte-copy memory
support, with no claim that an extra helper exists in the target.

## Libc trust boundary

In these ASTs memcpy is `EF_external "memcpy"`, with three arguments and a
pointer result. Its implementation is absent from CompCert's semantics.
`memcpy_model` is an explicit theorem premise, not an added axiom. Callers must
derive valid source/destination blocks, readable source bytes, writable destination
ranges, positive and representable sizes, address ranges without wraparound, and
absence of overlap from their legitimate input/frame contracts. The strengthened
contract requires these facts explicitly. The one-word, two-word and SHA byte-copy
callers derive them from their existing loads, alignment and range permissions;
zero-size SHA branches do not invoke the external call.
Permission, load and valid-block preservation follow from the model's storebytes
memory effect. The separately proved CompCert builtin copy witness has a different
ABI and does not discharge this library premise.

A conditional equivalence under this contract is a legitimate result. Neither
changing C nor switching compiler flags to turn the call into a builtin is a
proof of the original external call. Hash-cache/environment projections and
static globals/dispatch facts must also be stated and justified at their actual
boundaries, not hidden as execution or output assumptions.

## Required chain and current status

Each jet needs its real generated C body linked to Clight execution, its memory
and output representations, and evaluation of the canonical Simplicity program.
The chain includes success/failure and the applicable cursor, prefix, permission
and framing facts. Final contracts must derive intermediate execution/output
facts from initial preconditions, preserve legitimate inputs and retain their
conclusions. Review the actual specification definitions against the canonical
programs; compilation, axiom sets and snapshots alone do not establish fidelity.

The experimental delta is 101 commits and 126 added files relative to the common
base. Its new modules were absent from both build/audit manifests. They are now
registered for compilation and kernel/assumption/contract checking. Registration
is not final acceptance. The read8s/write8s oracle lemmas and symbolic soundness
pass the final build and kernel audit on this target. C-versus-integer normalization and byte/limb
results remain support until linked to canonical jet specifications. SHA and
Bitcoin results retaining libc/global-state premises must be reported with them.

Current source bookkeeping finds 242 entries without an extra libc premise,
104 entries conditional on libc, and 187 missing entries out of 533 declarations.
The restored target passes final acceptance against the reviewed snapshots,
without update flags (exit 0). See `JET_ACCEPTANCE.md` for the audited fingerprint. The remaining canonical bridges are listed in
`JET_FIDELITY_REVIEW.md`. No new direct coverage is claimed from integer models, symbolic
trees, retired helper proofs or unreviewed experimental theorem names. The completed consolidation review preserves these boundaries when integrating
and publishing the checked work.
