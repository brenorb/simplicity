# The complete public C jet surface and both registration catalogs, for the
# inventory gate in the otherwise Coq-only derivations.
{ lib }:
lib.sourceByRegex ./. [
  "C" "C/jets.h"
  "C/bitcoin" "C/bitcoin/bitcoinJets.h" "C/bitcoin/primitiveJetNode.inc"
  "C/elements" "C/elements/elementsJets.h" "C/elements/primitiveJetNode.inc"
]
