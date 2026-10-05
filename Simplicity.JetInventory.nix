# Production C and canonical Haskell inputs, retained in Coq-only builds
# for inventory, primitive identity and immutable source-target checks.
{ lib }:
lib.sourceFilesBySuffices
  (lib.sourceByRegex ./. [ "C" "C/.*" "Haskell" "Haskell/.*" ])
  [ ".c" ".h" ".inc" ".S" ".s" ".hs" ]
