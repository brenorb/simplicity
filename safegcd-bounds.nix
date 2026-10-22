{lib, stdenv, fetchFromGitHub, coq,
 cheating ? true, definitionsOnly ? false
} :
stdenv.mkDerivation {
  name = if definitionsOnly then "safegcd-definitions" else "safegcd-bounds-coq-divsteps";
  src = fetchFromGitHub {
    owner = "sipa";
    repo = "safegcd-bounds";
    rev ="06abb7f7aba9b00eb4ead96bdd7dbcc04ec45c4f";
    sparseCheckout = [
      "coq/divsteps"
    ];
    hash = "sha256-I+1TFBJOQxro09hkHBdCrLptoq06RYaeBz5PbPLzjGA=";
    name = "safegcd-bounds";
  };
  sourceRoot = "safegcd-bounds/coq/divsteps";

  ${if cheating && !definitionsOnly then "postPatch" else null} = ''
     substituteInPlace divsteps724.v --replace-fail "Time Qed." "Admitted."
  '';

  buildInputs = [ coq ];

  enableParallelBuilding = true;
  buildFlags = lib.optional definitionsOnly "divsteps_def.vo";

  preBuild = ''
    coq_makefile -f _CoqProject -o Makefile
  '';

  installFlags = "COQLIBINSTALL=$(out)/lib/coq/${coq.coq-version}/user-contrib/";
  ${if definitionsOnly then "installPhase" else null} = ''
    runHook preInstall
    mkdir -p "$out/lib/coq/${coq.coq-version}/user-contrib/divsteps"
    cp divsteps_def.v divsteps_def.vo "$out/lib/coq/${coq.coq-version}/user-contrib/divsteps/"
    runHook postInstall
  '';
}
