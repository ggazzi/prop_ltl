{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system}; in
      rec {
        packages = {
          # default = packages.foobar;
          # Add derivations here
        };

        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [ elixir erlang elixir_ls ];
        };
      }
    );
}
