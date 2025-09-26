# helpful: https://blog.jethro.dev/posts/ocaml_emacs_nixos/
# also https://ryantm.github.io/nixpkgs/languages-frameworks/ocaml/
# also https://dimitrije.website/posts/2023-03-04-nix-ocaml.html
# also https://nixos.wiki/wiki/OCaml
{
  description = "OCAML dev environment and myhello package";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, utils }: utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs { inherit system; config.allowUnfree = true; };
      fs = pkgs.lib.fileset;
      ocamlpkgs = pkgs.ocamlPackages;
      cudapkgs = pkgs.cudaPackages;
      ocamlInit = pkgs.writeText "ocamlinit" ''
          #use "topfind";;
          #thread;;
          #camlp4o;;
          #require "core";;
          #require "core.syntax";;
      '';
      sourceFiles = fs.unions [ ./. ];
    in {
      devShells.default = pkgs.mkShell {
        dontDetectOcamlConflicts = true;
        nativeBuildInputs = [
          pkgs.opam
          ocamlpkgs.containers
          ocamlpkgs.containers-data
          ocamlpkgs.core
          ocamlpkgs.core_extended
          ocamlpkgs.dune_3
          ocamlpkgs.findlib
          ocamlpkgs.graphics
          ocamlpkgs.mdx
          ocamlpkgs.merlin
          ocamlpkgs.menhir
          ocamlpkgs.ocaml
          ocamlpkgs.ocamlformat
          ocamlpkgs.ocaml-lsp
          ocamlpkgs.ocp-indent
          ocamlpkgs.odoc
          ocamlpkgs.ppxlib
          ocamlpkgs.ppx_deriving
          ocamlpkgs.ppx_deriving_yaml
          ocamlpkgs.re2
          ocamlpkgs.utop
          ocamlpkgs.yaml
          ocamlpkgs.yojson
          cudapkgs.cuda_nvcc
          cudapkgs.cuda_cudart
        ];
        UTOP_SITE_LISP = "${ocamlpkgs.utop}/share/emacs/site-lisp";
        MERLIN_SITE_LISP = "${ocamlpkgs.merlin}/share/emacs/site-lisp";
        OCP_INDENT_SITE_LISP="${ocamlpkgs.ocp-indent}/share/emacs/site-lisp";
        OCAMLFORMAT_SITE_LISP="${ocamlpkgs.ocamlformat}/share/emacs/site-lisp";
        OCAMLINIT = "${ocamlInit}";        
        shellHook = ''
          SHELL=${pkgs.bashInteractive}/bin/bash
          export PS1="gts.ocaml.nix: "
          alias utop="utop -init ${ocamlInit}"
          alias ocaml="ocaml -init ${ocamlInit}"
       '';
      };
    
      packages.myhello = ocamlpkgs.buildDunePackage {
        pname = "remora";
        version = "0.1";
        duneVersion = "3";
        src = ./.;
      };

      }
  );
}
