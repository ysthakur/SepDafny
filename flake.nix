{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    haskell-flake.url = "github:srid/haskell-flake";
  };
  outputs = inputs@{ self, nixpkgs, flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = nixpkgs.lib.systems.flakeExposed;
      imports = [ inputs.haskell-flake.flakeModule ];

      perSystem = { self', pkgs, ... }: {

        # Typically, you just want a single project named "default". But
        # multiple projects are also possible, each using different GHC version.
        haskellProjects.default = {
          # The base package set representing a specific GHC version.
          # By default, this is pkgs.haskellPackages.
          # You may also create your own. See https://community.flake.parts/haskell-flake/package-set
          basePackages = pkgs.haskellPackages;

          # Extra package information. See https://community.flake.parts/haskell-flake/dependency
          #
          # Note that local packages are automatically included in `packages`
          # (defined by `defaults.packages` option).
          #
          packages = {
            parsec.source = "3.1.17.0";
          };
          settings = {
            #  aeson = {
            #    check = false;
            #  };
            #  relude = {
            #    haddock = false;
            #    broken = false;
            #  };
            # fourmolu = { super, ...}: { custom = _: super.fourmolu_0_14_0_0; };
          };

          devShell = {
            # Programs you want to make available in the shell.
            # Default programs can be disabled by setting to 'null'
            # tools = hp: { fourmolu = hp.fourmolu; ghcid = null; };

            hlsCheck.enable = pkgs.stdenv.isDarwin; # On darwin, sandbox is disabled, so HLS can use the network.

            mkShellArgs = {
              buildInputs = with pkgs; [
                dafny
                dotnet-sdk
                icu70
                openssl
                openssh
              ];
              shellHook =
                let libraryPath = pkgs.lib.makeLibraryPath [ pkgs.openssl pkgs.openssl.dev ];
                in ''
                  alias cabal="cabal --disable-optimization --disable-documentation --disable-profiling"
                  export LD_LIBRARY_PATH=${libraryPath}
                  export PATH="./z3/bin:$PATH"
                '';
            };
          };
        };

        # haskell-flake doesn't set the default package, but you can do it here.
        packages.default = self'.packages.miniDafny;
      };
    };
}

