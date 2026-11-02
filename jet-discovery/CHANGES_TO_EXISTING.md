# Changes to existing code

None.  Every file this work adds is under `jet-discovery/`; no file outside it was modified
(`git diff master --stat -- . ':!jet-discovery'` is empty).

Workarounds used instead of changing the library (GOAL.md, minimal-change process step 1):

| need | workaround |
| --- | --- |
| The Bitcoin `Jet TermWeight` instance lives in a non-exported Backpack module | Restated the two-line instance in `src/JetDiscovery/Cost.hs` (no module imports the original, so they never meet) |
| Build against the in-tree library without editing `Simplicity.cabal` | A separate cabal project (`cabal.project`: `packages: ./ ../`) and `shell.nix` reusing `../default.nix`'s GHC package set |
| Primitives-only and ablated jet sets, candidate jets | New `JetType` instances wrapping the existing one (`src/JetDiscovery/JetSets.hs`, `src/JetDiscovery/WhatIf.hs`) |
