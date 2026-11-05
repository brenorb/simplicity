# Primary contract growth sources (inert data)

`provenance.json` inventories all30 selected files from16 repositories, with exact
immutable revision, source URL, SHA256 and source SPDX/repository license records.
The downloaded Solidity, Rust and Vyper sources are outside the build path and
have never been executed. License text is retained as data; no absent or custom
license is assumed permissive. The two ERC specifications declare their grants
in their own copyright sections.

`revision-pins.json` records the16 exact branch commits resolved with the GitHub
connector after the unauthenticated API returned HTTP403 rate limits.
`path-discovery.json` records full untruncated tree-based basename matches for
the source paths that needed discovery. The retrieval script then names the
actual on-chain implementation paths explicitly, excluding CLI, generated client
and test copies. The old guessed Curve optimized-math filename was replaced by
the real `TwocryptoMath.vy`/`Twocrypto.vy` sources. There are no remaining retrieval
gaps among these30 selected files. This is not a full repository scan.

Reproduce source retrieval with `python3 tools/vendor_growth_specs.py` from
`jet-discovery/`; the checked-in revision pins keep it immutable. Files are
read only as specifications by the implementation workflow. Source coverage,
application independence, deployment assumptions and implementation gates are
in `reports/CONTRACT-GROWTH-SCOPES.md`.

`dependency-provenance.json` adds33 successfully retrieved selected imports and
retains three404 path guesses explicitly. Pendle PYIndex was found at
`contracts/core/StandardizedYield/PYIndex.sol`; its guessed math path is not an
access claim. CoW Signing is retained from its actual `mixins/` path, with the404 guess still recorded. A guessed
market-maker clone factory is outside the pricing path and was not substituted
for a real implementation. Full repository coverage is not implied.

The LMSR imported Fixed192x64 dependency required a historical source pin. The
market-maker lockfile names exact `@gnosis.pm/util-contracts` version3.0.0-alpha.3.
Its integrity equals the authoritative npm metadata, whose gitHead is
`ead0a32ba6eff3d619dfb711466b46f4c54ed6c1`. Both Fixed192x64Math and SignedSafeMath
are retained at that commit, with LGPL3 license and per-file hashes in
`lmsr-dependency-provenance.json`. The modern main/v3.0.0 source no longer has the
required Fixed192x64 file and was not silently used. No package was installed or
executed; all metadata, lockfile and source files are inert data.
