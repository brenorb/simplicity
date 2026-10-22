{ coq, safegcd-bounds, lib, vst, coqprime, stdenv, python3
, alectryon ? null
, serapi ? null
}:
assert alectryon != null -> serapi != null;
stdenv.mkDerivation {
  name = "Simplicity-coq-0.0.0";
  # Source checks read C, Haskell and Coq through their shared repository root.
  src = lib.sourceFilesBySuffices
    (lib.sourceByRegex ./. ["C" "C/.*" "Haskell" "Haskell/.*" "Coq" "Coq/.*"])
    ["_CoqProject" ".jets" ".jets-regression" ".v" ".c" ".h" ".inc" ".S" ".s"
     ".hs" ".in" ".sh" ".py" ".txt" ".tsv" ".expected" ".contracts" ".assumptions" ".md"];
  postUnpack = ''
    sourceRoot="$sourceRoot/Coq"
  '';
  outputs = [ "out" ] ++ lib.optional (alectryon != null) "doc";
  postConfigure = ''
    coq_makefile -f _CoqProject -o CoqMakefile
  '';

  buildInputs = [ coq ];
  nativeBuildInputs = [ python3 ] ++ lib.optional (alectryon != null) serapi;
  propagatedBuildInputs = [ safegcd-bounds vst coqprime ];
  enableParallelBuilding = true;
  makefile = "CoqMakefile";
  postBuild = lib.optional (alectryon != null) ''
    ${alectryon}/bin/alectryon --frontend coq --output-directory $doc --webpage-style windowed -R C C \
    C/secp256k1/spec_int128.v C/secp256k1/verif_int128_impl.v \
    C/divstep.v C/secp256k1/spec_modinv64.v C/secp256k1/verif_modinv64_impl.v
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
