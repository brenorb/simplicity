# Focused build of the jet implementation-to-specification proofs:
# the Simplicity library plus Coq/C/jet_*.v, without the secp256k1 and modinv
# verifications of the full `coq` derivation.  Runs coqchk over every module
# that contains a public theorem (Coq/C/jet_public_theorems.txt).
{ coq, vst, compcert, lib, stdenv }:
stdenv.mkDerivation {
  name = "Simplicity-coq-jets-0.0.0";
  src = lib.sourceFilesBySuffices
      (lib.sourceByRegex ./Coq ["_CoqProject.jets" "C" "C/.*" "Simplicity" "Simplicity/.*" "Util" "Util/.*"])
    ["_CoqProject.jets" ".v" "jet_public_theorems.txt"];

  buildInputs = [ coq ];
  propagatedBuildInputs = [ vst compcert ];
  enableParallelBuilding = true;
  makefile = "CoqMakefile";

  postConfigure = ''
    coq_makefile -f _CoqProject.jets -o CoqMakefile
  '';

  doCheck = true;
  checkPhase = ''
    mods=$(awk '!/^#/ && NF==2 {print $1}' C/jet_public_theorems.txt | sort -u | tr '\n' ' ')
    coqchk -silent -R C C -Q Simplicity Simplicity $mods
  '';

  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";
  meta = {
    license = lib.licenses.mit;
  };
}
