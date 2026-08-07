{
  description = "Intrinsic Verification of Parsers and Formal Grammar Theory in Dependent Lambek Calculus (Agda implementation)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    agda.url = "github:agda/agda";
    cubical = {
      url = "github:agda/cubical";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        flake-utils.follows = "flake-utils";
        agda.follows = "agda";
      };
    };
    cubical-categorical-logic = {
      url = "github:um-catlab/cubical-categorical-logic";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        flake-utils.follows = "flake-utils";
        agda.follows = "agda";
        cubical.follows = "cubical";
      };
    };
  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
    cubical,
    cubical-categorical-logic,
    ...
  }:
    let
      overlay = final: prev: {
        grammars-and-semantic-actions = final.agdaPackages.mkDerivation {
          pname = "grammars-and-semantic-actions";
          version = "0.1";

          src = final.lib.cleanSourceWith {
            filter = name: _type:
              !(final.lib.hasSuffix ".nix" name)
              && !(final.lib.hasSuffix "flake.lock" name)
              && !(final.lib.hasSuffix ".envrc" name);
            src = final.lib.cleanSource ./src;
          };

          LC_ALL = "C.UTF-8";

          nativeBuildInputs = [ final.agdaWithCubicalCategoricalLogic ];

          buildPhase = ''
            runHook preBuild
            make check
            runHook postBuild
          '';

          meta = {
            description = "Cubical Agda formalisation of Dependent Lambek Calculus";
          };
        };
      };
    in
    { overlays.default = overlay; } //
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [
            cubical.inputs.agda.overlays.default
            cubical.overlays.default
            cubical-categorical-logic.overlays.default
            overlay
          ];
        };

        # Typst toolchain for `doc/`.  Kept flake-local on purpose: nothing
        # typst-related is installed globally, so the version that builds the
        # docs is the one pinned in flake.lock.
        #
        # NOTE: deliberately plain `typst`, not `typst.withPackages`.
        # `withPackages` works for dependency-free packages (curryst,
        # ctheorems), but it cannot supply `fletcher`: nixpkgs puts
        # `cetz 0.3.4` inside fletcher's closure while shipping
        # `oxifmt 1.0.0` next to it, and cetz 0.3.4 imports `oxifmt 0.2.1`
        # by exact version.  Typst then tries to install the missing version
        # into the read-only store and fails.  Left to resolve `@preview`
        # itself, typst fetches the exact pins into its own cache and
        # everything -- fletcher included -- builds.
        #
        # Cost: the first `typst compile` needs the network.  If you ever
        # want that closed, vendor the packages under `doc/packages/` and
        # pass `--package-path`; `withPackages` is not the lever.
        typstEnv = pkgs.typst;
      in
      {
        packages = {
          inherit (pkgs) grammars-and-semantic-actions;
          default = pkgs.grammars-and-semantic-actions;
        };

        # Development shell: Agda with cubical + cubical-categorical-logic
        # plus fix-whitespace. Activate via `nix develop` or direnv.
        #
        # To use a local checkout of one of the dependencies, run e.g.:
        #   nix develop --override-input cubical path:../Cubical
        #   nix develop --override-input cubical-categorical-logic \
        #                path:../cubical-categorical-logic
        devShells.default = pkgs.mkShell {
          nativeBuildInputs = [
            pkgs.agdaWithCubicalCategoricalLogic
            pkgs.haskellPackages.fix-whitespace

            # Docs.  `tinymist` is the LSP server; Emacs finds it through
            # envrc/direnv rather than from a global profile, so it exists
            # only inside this shell.
            typstEnv
            pkgs.tinymist
          ];

          shellHook = ''
            echo "grammars-and-semantic-actions dev shell"
            echo "  agda:  $(agda --version 2>/dev/null | head -n1)"
            echo "  typst: $(typst --version 2>/dev/null | head -n1)"
          '';
        };
      }
    );
}
