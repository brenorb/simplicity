# Development shell for jet-discovery.
# Reuses the GHC package set of the in-tree Simplicity derivation (../default.nix)
# and adds cabal-install, so `cabal build` can compile the in-tree library from source.
{ nixpkgs ? import <nixpkgs> {} }:
let
  simplicity = import ../. { inherit nixpkgs; };
  hs = simplicity.haskell;
  ghcEnv = simplicity.haskellPackages.ghcWithPackages
             (p: hs.buildInputs ++ hs.propagatedBuildInputs);
in
  nixpkgs.mkShell {
    packages = [ ghcEnv nixpkgs.cabal-install ];
  }
