This repo is an implementation of [Freer Monads](http://okmij.org/ftp/Haskell/extensible/more.pdf) 

# Build
1. Make sure you have the [nix package manager](https://nixos.org/nix/) installed.


2. (Optional) If your are on MacOS, you can use [cachix](https://github.com/cachix/cachix) and use our pre-built cache.
For this, all you have to do is to run

`$ nix-env -iA cachix -f https://github.com/NixOS/nixpkgs/tarball/889c72032f8595fcd7542c6032c208f6b8033db6`
`$ cachix use refine-free`


3. Build

`$ nix-build`

In order to run Proof General with the correct nix configuration we still need a couple of extra steps:

4. Install (Emacs-direnv)[https://github.com/wbolster/emacs-direnv]

`M-x package-install RET direnv RET`

5. Add the [this script](https://github.com/jwiegley/nix-config/blob/master/bin/use_nix.sh) to your path 

6. Add the following configuration to your .emacs file

```(use-package direnv
  :demand t
  :config
  (direnv-mode)
  (eval-after-load 'flycheck
    '(setq flycheck-executable-find
           (lambda (cmd)
             (direnv-update-environment default-directory)
             (executable-find cmd))))
  :hook
  (coq-mode . direnv-update-environment))```

7. Run nix-shell

`$ nix-shell`

8. Now you can finally Proof General with the correct buffer

`$ emacs src/Refine.v`

PS.: Remember to always run `nix-shell` before emacs.
