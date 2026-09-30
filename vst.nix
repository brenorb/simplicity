{lib, stdenv, fetchFromGitHub, coq, compcert,
 ignoreCompcertVersion ? compcert.version=="3.14" # Temporarily allow compcert 3.14
, shaOnly ? false
} :
stdenv.mkDerivation ({
  name = if shaOnly then "vst-sha-library-2.14" else "vst-sha256-2.14";
  src = fetchFromGitHub {
    owner = "PrincetonUniversity";
    repo = "VST";
    rev ="v2.14";
    hash = "sha256-NHc1ZQ2VmXZy4lK2+mtyeNz1Qr9Nhj2QLxkPhhQB7Iw";
  };

  buildInputs = [ coq ];
  propagatedBuildInputs = [ compcert ];

  patches = [ ];

  postPatch = ''
    substituteInPlace util/coqflags \
      --replace "\`/bin/pwd\`" "$out/lib/coq/${coq.coq-version}/user-contrib/VST"
    patchShebangs --build util/*
  '';

  enableParallelBuilding = true;

  makeFlags =
    lib.optional ignoreCompcertVersion "IGNORECOMPCERTVERSION=true" ++
  [
    "COMPCERT=inst_dir"
    "COMPCERT_INST_DIR=${compcert}/lib/coq/${coq.coq-version}/user-contrib/compcert"
    "INSTALLDIR=$(out)/lib/coq/${coq.coq-version}/user-contrib/VST"
  ];

  buildFlags = if shaOnly then
    [ "sha/general_lemmas.vo" "sha/SHA256.vo" "sha/functional_prog.vo" ]
    else [ "default_target" "sha" ];

  postBuild = lib.optionalString (!shaOnly) ''
    $CC -c sha/sha.c -o sha/sha.o
  '';

  postInstall = lib.optionalString (!shaOnly) ''
    install -d "$out/lib/coq/${coq.coq-version}/user-contrib/sha"
    find sha -name \*.vo -exec sh -c '
     install -m 0644 -T "$0" "$out/lib/coq/${coq.coq-version}/user-contrib/$0"
     install -m 0644 -T "''${0%.vo}.v" "$out/lib/coq/${coq.coq-version}/user-contrib/''${0%.vo}.v"
    ' {} \;
    install -d "$out/lib/sha"
    install -m 0644 -t "$out/lib/sha" "sha/sha.o" "sha/sha.h"
    install -d "$out/share"
    install -m 0644 -t "$out/share" "_CoqProject-export"
  '';
} // lib.optionalAttrs shaOnly {
  # Install only the compiled dependency closure, retaining logical namespaces.
  installPhase = ''
    runHook preInstall
    contrib="$out/lib/coq/${coq.coq-version}/user-contrib"
    find . -name '*.vo' | while read -r file; do
      rel="''${file#./}"
      install -D -m 0644 "$file" "$contrib/VST/$rel"
      install -D -m 0644 "''${file%.vo}.v" "$contrib/VST/''${rel%.vo}.v"
      case "$rel" in
        sha/*)
          install -D -m 0644 "$file" "$contrib/$rel"
          install -D -m 0644 "''${file%.vo}.v" "$contrib/''${rel%.vo}.v"
          ;;
      esac
    done
    runHook postInstall
  '';
})
