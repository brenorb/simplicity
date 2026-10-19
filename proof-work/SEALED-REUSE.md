# Reusing sealed proof bases after an unrelated proof repair

```sh
python3 -B proof-work/check-sealed-jet-bases.py all
```

This read-only check validates the exact sealed field-multiplication, Bitcoin
identity-diagnostic, borrowed-region and repaired-count source/object/kernel
inputs. It also checks matching current source mirrors and the unchanged
production/canonical/generation target. It does **not** rerun the kernel or
certify the complete current checkout, accepted registry or normal build.

The original audit scripts also checked that the entire main checkout and
unrelated staged patch remained unchanged while they ran. Those observations
are valid only for their exact historical input inventories. The later
one-line count-bridge proof repair intentionally changes one unrelated main
proof source; an old whole-checkout sentinel must reject that changed checkout.
Do not edit its receipts or pretend the old complete input inventory matches.

Instead, this separate reuse check follows the frozen source/object and
successful-kernel identities themselves, checks the command and inherited
library context, and compares every available loaded-source mirror. Field
multiplication does not load the Bitcoin count bridge, so that proof's loaded
inputs are unchanged. The count derivative includes the exact promoted repair.
No historical receipt is rewritten or widened to cover a different proof.

This is a reuse check for four named, already checked bases—not a general
acceptance mechanism or permission to reuse stale objects. Changed source
closures require fresh compilation and kernel verification. The unresolved
Bitcoin identity gate and value-domain proof-build failure remain visible in
`secp-field-acceptance`; this tool cannot turn either failure into acceptance.
