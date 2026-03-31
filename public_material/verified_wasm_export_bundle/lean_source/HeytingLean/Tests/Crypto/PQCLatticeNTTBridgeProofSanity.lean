import HeytingLean.Crypto.Lattice.NTTBridgeProof

/-!
# PQC lattice bridge sanity: NTT bridge proof

This compile-time sanity check ensures the main Gap 1 bridge theorem elaborates as part of the
default `AllSanity` umbrella.
-/

namespace HeytingLean.Tests.Crypto.PQCLatticeNTTBridgeProofSanity

open HeytingLean.Crypto.Lattice.NTTBridge

example : nttIterative_matches_quadraticSpec :=
  HeytingLean.Crypto.Lattice.NTTBridgeProof.nttIterative_matches_quadraticSpec_proved

end HeytingLean.Tests.Crypto.PQCLatticeNTTBridgeProofSanity

