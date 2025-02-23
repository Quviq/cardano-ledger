############################################################################
# Builds Haskell packages with Haskell.nix
############################################################################
{ lib
, stdenv
, pkgs
, haskell-nix
, CHaP
, buildPackages
, config ? {}
# GHC attribute name
, compiler ? config.haskellNix.compiler or "ghc926"
# Enable profiling
, profiling ? config.haskellNix.profiling or false
}:
let

  src = haskell-nix.haskellLib.cleanGit {
      name = "cardano-ledger";
      src = ../.;
  };

  # The cardano-mainnet-mirror used during testing
  cardano-mainnet-mirror = import ./cardano-mainnet-mirror.nix {inherit pkgs;};

  # This creates the Haskell package set.
  # https://input-output-hk.github.io/haskell.nix/user-guide/projects/
  pkgSet = haskell-nix.cabalProject {
    inherit src;
    inputMap = { "https://input-output-hk.github.io/cardano-haskell-packages" = CHaP; };
    compiler-nix-name = compiler;
    modules = [
      {
        # Use our forked libsodium from iohk-nix crypto overlay.
        packages.cardano-crypto-class.components.library.pkgconfig = lib.mkForce [ [ pkgs.libsodium-vrf pkgs.secp256k1 ] ];
        packages.cardano-crypto-praos.components.library.pkgconfig = lib.mkForce [ [ pkgs.libsodium-vrf pkgs.secp256k1 ] ];
        packages.byron-spec-chain.configureFlags = [ "--ghc-option=-Werror" ];
        packages.byron-spec-ledger.configureFlags = [ "--ghc-option=-Werror" ];
        packages.delegation.configureFlags = [ "--ghc-option=-Werror" ];
        packages.non-integral.configureFlags = [ "--ghc-option=-Werror" ];
        packages.cardano-ledger-shelley.configureFlags = [ "--ghc-option=-Werror" ];
        packages.cardano-ledger-shelley-ma.configureFlags = [ "--ghc-option=-Werror" ];
        packages.cardano-ledger-shelley-ma-test.configureFlags = [ "--ghc-option=-Werror" ];
        packages.cardano-ledger-shelley-ma-test.components.tests.cardano-ledger-shelley-ma-test.build-tools = [pkgs.cddl pkgs.cbor-diag];
        packages.small-steps.configureFlags = [ "--ghc-option=-Werror" ];
        packages.cardano-ledger-shelley-test.components.tests.cardano-ledger-shelley-test.build-tools = [pkgs.cddl pkgs.cbor-diag];
        packages.cardano-ledger-alonzo-test.components.tests.cardano-ledger-alonzo-test.build-tools = [pkgs.cddl pkgs.cbor-diag];
        packages.cardano-ledger-babbage-test.components.tests.cardano-ledger-babbage-test.build-tools = [pkgs.cddl pkgs.cbor-diag];
        enableLibraryProfiling = profiling;
        # Disable doctests for now (waiting for https://github.com/input-output-hk/haskell.nix/pull/427):
        packages.small-steps.components.tests.doctests.buildable = lib.mkForce false;
        packages.small-steps-test.components.tests.doctests.buildable = lib.mkForce false;
        packages.byron-spec-ledger.components.tests.doctests.buildable = lib.mkForce false;

        packages.cardano-ledger-byron = {
          configureFlags = [ "--ghc-option=-Werror" ];
          components = {
            tests.cardano-ledger-byron-test = {
              preCheck = ''
                export CARDANO_MAINNET_MIRROR="${cardano-mainnet-mirror}/epochs"
                cp ${../eras/byron/ledger/impl/mainnet-genesis.json} ./mainnet-genesis.json
              '';
              build-tools = [ pkgs.makeWrapper ];
              testFlags = [ "--scenario=ContinuousIntegration" ];
            };
          };
        };

      }
    ];
  };
in
  pkgSet
