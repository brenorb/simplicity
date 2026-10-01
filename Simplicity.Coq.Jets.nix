# Focused build of the jet implementation-to-specification proofs:
# the Simplicity library plus Coq/C/jet_*.v, without the secp256k1 and modinv
# verifications of the full `coq` derivation.  Runs coqchk over every module
# that contains a public theorem (Coq/C/jet_public_theorems.txt).
{ coq, vst, compcert, lib, stdenv, python3 }:
stdenv.mkDerivation {
  name = "Simplicity-coq-jets-0.0.0";
  src = lib.sourceFilesBySuffices
      (lib.sourceByRegex ./Coq ["_CoqProject.*" ".*\\.sh" ".*\\.py" "C" "C/.*" "Simplicity" "Simplicity/.*" "Util" "Util/.*"])
    ["_CoqProject" "_CoqProject.jets" ".v" ".sh" ".py" ".txt" ".tsv" ".expected"];

  buildInputs = [ coq ];
  nativeBuildInputs = [ python3 ];
  propagatedBuildInputs = [ vst compcert ];
  enableParallelBuilding = true;
  makefile = "CoqMakefile";

  postConfigure = ''
    coq_makefile -f _CoqProject.jets -o CoqMakefile
  '';

  doCheck = true;
  checkPhase = ''
    JET_C_REPO=${import ./Simplicity.JetInventory.nix { inherit lib; }} \
      JET_USE_COQPATH=1 bash check-jets.sh --no-build
  '';

  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";
  meta = {
    license = lib.licenses.mit;
  };
}
