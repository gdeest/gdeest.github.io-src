with { pkgs = import ./nix {}; };
pkgs.haskellPackages.shellFor
  { packages = ps: [ ps.gdeest-blog ];
    buildInputs = [ pkgs.niv pkgs.cabal-install ];
    withHoogle = false;
  }
