{ sources ? import ./sources.nix }:
with
  { overlay = _: pkgs:
      { inherit (import sources.niv {}) niv;
        packages = pkgs.callPackages ./packages.nix {};
      };
  };
import sources.nixpkgs
  { overlays = [
      overlay
      (self: super:
        { haskellPackages =
            super.haskellPackages.extend
              (super.haskell.lib.packageSourceOverrides
                { gdeest-blog = super.lib.cleanSource ../. ; }
              );
        }
      )
    ] ; config = {}; }
