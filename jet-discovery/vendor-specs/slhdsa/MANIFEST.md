# FIPS 205 standard SLH-DSA baseline provenance

Official FIPS 205 was published on 2024-08-13. The official NIST ACVP repository
is pinned at `975de31eb83d87039ec88934fdc47d8c312b892d`. All 42 SHA2-128s cases
across three groups are retained, including 14 pre-hash cases outside the pure
baseline. The independent reference checks all 28 pure/internal cases.
Simplicity's selected published fixture is external-pure group 19, case 266
(24-byte message and 255-byte context).

The full 30,513,796-byte all-parameter prompt is not duplicated here. Its SHA-256
is `4e7beb1233e47baa0acdd36417c66c45811aa40a4e32ffdb1a35d93b13b289fb`.
`tools/extract_slh_acvp.py` rejects different bytes and reproduces the complete
128s subset from that pinned source. No downloaded code is executed.

National Institute of Standards and Technology is the source of the ACVP data.
Its complete license/disclaimer notice is preserved in `acvp-README.md`.
Modification notice (2026-11-05): selection of complete 128s groups, joining
expected results, and conversion to table/fixed fixture; source field values
remain unchanged. The FIPS publication is separate; no additional PDF license
notice was located or inferred. `manifest.json` records every archived file's
URL, revision, byte length, checksum and archive/derivation timestamp.
