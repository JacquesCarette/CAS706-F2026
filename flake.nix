{
  description = "CAS 706 Flake";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";
  inputs.flake-parts.url = "github:hercules-ci/flake-parts";

  outputs = inputs:
    inputs.flake-parts.lib.mkFlake { inputs = inputs; }
      {
        systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
        perSystem = { pkgs, lib, ... }: let
          # See https://nixos.org/manual/nixpkgs/stable/#agda
          agdaWithStdlib = pkgs.agdaPackages.agda.withPackages (agdaPkgs: [
            agdaPkgs.standard-library
          ]);
          cas706 = pkgs.agdaPackages.mkDerivation {
            pname = "CAS706";
            version = "0.0.1";
            meta = {
              description = "Course materials for McMaster CAS706";
            };

            # Strip out any files that bind BUILTINs from the build: these break --build-library.
            src = lib.cleanSourceWith {
              filter = name: _type:
                !(lib.hasSuffix "Equality.lagda.md" name)
                && !(lib.hasSuffix "Naturals.lagda.md" name);
              src = ./filled;
            };
            buildInputs = [
              pkgs.agdaPackages.standard-library
            ];
          };
        in {
          packages.default = cas706;
          devShells.default = pkgs.mkShell {
            nativeBuildInputs = [
              agdaWithStdlib
            ];
          };
        };
      };
}
