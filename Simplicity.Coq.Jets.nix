# Focused build of the jet implementation-to-specification proofs:
# the Simplicity library plus Coq/C/jet_*.v and shared integer divstep lemmas,
# without the VST secp256k1 verifications of the full `coq` derivation.
# Runs coqchk over every built jet
# module and compares the reviewed public contracts and assumptions.
{ coq, vst, compcert, coqprime, safegcd-definitions, lib, stdenv, python3 }:
stdenv.mkDerivation {
  name = "Simplicity-coq-jets-0.0.0";
  # Source checks read C, Haskell and Coq through their shared repository root.
  src = lib.sourceFilesBySuffices
    (lib.sourceByRegex ./. ["C" "C/.*" "Haskell" "Haskell/.*" "Coq" "Coq/.*"])
    ["_CoqProject" ".jets" ".jets-regression" ".v" ".c" ".h" ".inc" ".S" ".s"
     ".hs" ".in" ".sh" ".py" ".txt" ".tsv" ".expected" ".contracts" ".assumptions" ".md"];
  postUnpack = ''
    sourceRoot="$sourceRoot/Coq"
  '';

  buildInputs = [ coq ];
  nativeBuildInputs = [ python3 ];
  propagatedBuildInputs = [ vst compcert coqprime safegcd-definitions ];
  enableParallelBuilding = true;
  makefile = "CoqMakefile";

  postConfigure = ''
    coq_makefile -f _CoqProject.jets -o CoqMakefile
  '';

  doCheck = true;
  checkPhase = ''
    JET_USE_COQPATH=1 bash check-jets.sh --no-build
  '';

  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";
  meta = {
    license = lib.licenses.mit;
  };
}
