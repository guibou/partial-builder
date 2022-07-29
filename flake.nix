{
  description = "A very basic flake";

  outputs = { self, nixpkgs }: {

    packages.x86_64-linux =
      let pkgs = nixpkgs.legacyPackages.x86_64-linux;
      in { partial-builder = pkgs.haskellPackages.callCabal2nix "partial-builder" ./. { }; };
      devShell.x86_64-linux = self.packages.x86_64-linux.partial-builder.env.overrideAttrs (old: {
        buildInputs = old.buildInputs ++ [
          nixpkgs.legacyPackages.x86_64-linux.cabal-install
          nixpkgs.legacyPackages.x86_64-linux.haskellPackages.doctest
        ];
      });
  };
}
