# SHA jets of the Elements translation unit

The Elements program `C/jets_elements.v` is generated from a translation unit
that includes `sha256.c` and `elements/ops.c`. Every C definition mentioned by
the accepted SHA proof modules (`C/jet_sha*.v`) has the same Clight text there
as in the SHA unit (`check-definitions.py`: 66 definitions). This directory
uses that to obtain the SHA results for the Elements program without
re-proving them, and adds the Elements-specific pieces.

Nothing here is registered or accepted; no accepted source is edited. The
derived tree `tree/` (ignored by git) holds symbolic links to the accepted
sources, a copy of `jets_elements.v` under the module name `C.jets_sha`, and
its own compiled objects.

## What is proved

| Module | Content |
|---|---|
| `C/jet_elements_sha_program.v` | `elements_sha_program : jets_sha.prog = jets_elements.prog` and `elements_sha_genv : sha_ge = elements_ge` in the derived tree |
| `C/jet_elements_sha_jets.v` (generated) | the 14 accepted SHA jet theorems restated for `elements_ge` and the functions of `C.jets_elements` |
| `C/jet_elements_annex_hash_jet.v` (generated) | `annex_hash`: same C text and same program (`Programs.Elements.annexHash`) as Bitcoin |
| `C/jet_elements_tap_tags.v`, `…build_tapleaf_*`, `…make_tap*_exec`, `…build_tapbranch_*` (generated) | `build_tapleaf_simplicity`, `build_tapbranch` with the tags `TapLeaf/elements`, `TapBranch/elements` |
| `C/jet_elements_hash_jets.v` | the three theorems above restated for `elements_ge` |
| `startup/jet_elements_startup_state.v` (generated) | invariant `el_sha_startup_state` from `Genv.init_mem jets_elements.prog`; preserved by frame-contract calls |
| `startup/jet_elements_startup_jets.v` (generated) | 17 jets over the invariant, re-establishing it |
| `startup/jet_elements_startup_setup.v`, `…_executable.v`, `…_runs.v` (generated) | caller memory operations keep the invariant; each of the 17 jets runs on fresh frames for every input |

## Boundaries

- **Tag constants.** The generator recomputes prefix, tag hash and padded
  block for the Elements tags (after reproducing the accepted Bitcoin
  constants with the same code); Coq checks them by evaluating the canonical
  `hashBlock` (`el_tapleaf_tag_hash_eval`, `el_tapleaf_prefix_eval`,
  `el_tapleaf_tag_block_bytes` and the tapbranch counterparts).
- **Canonical programs.** `Programs/Elements.hs` and `Programs/Bitcoin.hs`
  define `buildTapleafSimplicity`, `buildTapbranch` and `annexHash` with the
  same text except for the tag strings. The Coq program terms are the ports
  already used by the accepted Bitcoin theorems with the Elements prefix
  constant.
- **A caller premise that the SHA unit does not need.** The tag arrays of
  `elements/ops.c` are writable and 17 and 19 bytes long. In the memory model
  a 16-byte frame record fits inside one, so "the destination frame record is
  not a tag array" cannot be derived from extents as it is for Bitcoin's 8-
  and 10-byte arrays. It is the explicit premise `el_frame_record_sep`,
  discharged for freshly allocated frames (`el_fresh_record_sep`) and for
  blocks a caller allocated itself (`el_owned_record_sep`). The word buffer
  needs no premise for outputs wider than 128 bits, which covers all 17 jets.
- **Kept premise.** `memcpy_model`, exactly as in the accepted theorems.
- **Not covered.** `outpoint_hash` and the other Elements hash jets differ
  from Bitcoin's C and programs; `build_taptweak` is a secp jet.

## Build and check

```bash
bash Coq/build-elements-sha.sh -j4
```

```bash
bash Coq/audit-elements-sha.sh
```

The start-up modules are built when `Coq/startup/prereq` has been extracted
by `build-startup.sh` (it needs `SHA_SUPPORT`; the two archived prerequisites
are verified by hash there). The audit regenerates every generated module and
compares, rejects admissions, checks assumption reports (six inherited
assumptions; eight for start-up results, as in `Coq/startup`) and runs
`coqchk` on the result modules with their dependency chains.

Never rebuild objects in `tree/` while `coqchk` is reading them.

## Receipts

See the end of this file; appended by hand from audit runs.

| Commit | Command | Result |
|---|---|---|
| `1a4b15fc` | `bash Coq/audit-elements-sha.sh` (first version) | assumption audit passed, 15 reports; `coqchk` passed for `jet_elements_sha_jets` and dependencies; 15 min |
| `d4214a5e` | `bash Coq/audit-elements-sha.sh` | generated modules current; assumption audit passed: 55 reports (18 within the six inherited assumptions, 37 start-up reports within eight); `coqchk` passed for `C.jet_elements_sha_jets`, `C.jet_elements_hash_jets` and the five `ElementsStartup` modules with dependencies; exit 0; 17 min |
