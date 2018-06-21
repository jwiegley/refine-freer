let inherit ((import <darwin> {}).pkgs)
      lib nixBufferBuilders
      coq_8_7 coqPackages_8_7;

      coq         = coq_8_7;
      coqPackages = coqPackages_8_7;

in with coqPackages; nixBufferBuilders.withPackages [
  coq coq.ocaml coq.camlp5 coq.findlib
  equations fiat_HEAD coq-haskell
]
