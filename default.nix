{ packages ? "coqPackages_8_8"

, rev      ? "89b618771ad4b0cfdb874dee3d51eb267c4257dd"
, sha256   ? "0jlyggy7pvqj2a6iyn44r7pscz9ixjb6fn6s4ssvahfywsncza6y"

, pkgs     ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

with pkgs.${packages}; pkgs.stdenv.mkDerivation rec {
  name = "refine-freer";
  version = "1.0";

  src =
    if pkgs.lib.inNixShell
    then null
    else if pkgs ? coqFilterSource
         then pkgs.coqFilterSource [] ./.
         else ./.;

  buildInputs = [
    coq coq.ocaml coq.camlp5 coq.findlib
    equations coq-haskell
    (category-theory.overrideAttrs (attrs: rec {
       name = "coq${coq.coq-version}-category-theory-${version}";
       version = "20181004";
       src = pkgs.fetchFromGitHub {
         owner = "jwiegley";
         repo = "category-theory";
         rev = "d5cf6c25de1c28bd71130965e3bb05a17a71301e";
         sha256 = "0f5sihgkgiiv974hls9dwg37782y6w10ly2ygq0mq962s84i4kg1";
         # date = 2018-10-04T15:39:49-07:00;
       };
       propagatedBuildInputs = [ coq ssreflect equations ];
     }))
    (fiat_HEAD.overrideAttrs (attrs: rec {
       name = "coq${coq.coq-version}-fiat-core-${version}";
       version = "20180514";
       src = pkgs.fetchFromGitHub {
         owner = "jwiegley";
         repo = "fiat-core";
         rev = "5d2d1fdfba7c3ed5a3120dad2415b0bb958b6d02";
         sha256 = "190v5sz8fmdhbndknq9mkwpj3jf570gzdibww7f76g81a34v3qli";
         fetchSubmodules = true;
         # date = 2018-05-14T10:05:32-07:00;
       };
       buildInputs = [ coq coq.ocaml coq.camlp5 coq.findlib
                       pkgs.git pkgs.python27 ];
     }))
  ];
  enableParallelBuilding = true;

  buildPhase = "make -j$NIX_BUILD_CORES";
  preBuild = "coq_makefile -f _CoqProject -o Makefile";
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  env = pkgs.buildEnv { name = name; paths = buildInputs; };
  passthru = {
    compatibleCoqVersions = v: builtins.elem v [ "8.6" "8.7" "8.8" ];
 };
}
