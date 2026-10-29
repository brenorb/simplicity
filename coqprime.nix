# Standard-integer certificates and finite curve groups; no bignums/native checker.
{ coq, lib, stdenv, fetchurl }:
stdenv.mkDerivation {
  pname = "coqprime-standard-checker";
  version = "8.17";
  src = fetchurl {
    url = "https://github.com/thery/coqprime/archive/431d7a66877cbe8688fc8864ef892369401440e1.tar.gz";
    sha256 = "cfd5845d37987cff2c0f028b3f9f18a80716e255ac6379b41af1ebfffae88d90";
  };
  buildInputs = [ coq ];
  enableParallelBuilding = true;
  makeFlags = [ "COQBIN=${coq}/bin/" ];
  buildFlags = [
    "src/Coqprime/PrimalityTest/PocklingtonCertificat.vo"
    "src/Coqprime/elliptic/SMain.vo"
    "src/Coqprime/elliptic/GZnZ.vo"
  ];
  installPhase = ''
    runHook preInstall
    contrib="$out/lib/coq/${coq.coq-version}/user-contrib"
    find src/Coqprime -name '*.vo' | while read -r file; do
      rel="''${file#src/}"
      install -D -m 0644 "$file" "$contrib/$rel"
      install -D -m 0644 "''${file%.vo}.v" "$contrib/''${rel%.vo}.v"
    done
    install -D -m 0644 LICENSE "$out/share/licenses/coqprime/LICENSE"
    runHook postInstall
  '';
  meta = {
    description = "CoqPrime standard-integer certificates and finite curve groups for jet proofs";
    homepage = "https://github.com/thery/coqprime";
    license = lib.licenses.lgpl21Only;
  };
}
