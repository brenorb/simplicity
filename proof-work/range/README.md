# Historical frame-range correction

The repaired range correction is integrated in the active proofs. This archive
preserves the original numbered patch series and later repair patches as
alternative development history. It does not describe current coverage.

The numbered series applies in order to
`8f186eef4b513d2e3640a9ba70dabb649ebaeb7e` and ends at
`00536113eb285b109f00c28a0fd22de66b05ec35`. That original candidate stops at
`jet_full_multiply8_layout.v:122`; the later repairs are separate patches.
Use a fresh external checkout for historical replay. The full old archive and
its patch/dependency metadata can be recovered as described in `../README.md`.
Current acceptance uses `bash Coq/check-jets.sh --accept`.
