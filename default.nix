{ packages ? "coqPackages_8_7"

, rev      ? "d7d31fea7e7eef8ff4495e75be5dcbb37fb215d0"
, sha256   ? "1ghb1nhgfx3r2rl501r8k0akmfjvnl9pis92if35pawsxgp115kv"

, pkgs     ? (import <darwin> {}).pkgs
# , pkgs     ? import (builtins.fetchTarball {
#     url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
#     inherit sha256; }) {
#     config.allowUnfree = true;
#     config.allowBroken = false;
#   }
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
    equations fiat_HEAD coq-haskell category-theory
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
