import HeytingLean.Tests.Crypto.PQCFHEZKSanity
import HeytingLean.Tests.Crypto.PQCLatticeNoiseSanity
import HeytingLean.Tests.Crypto.PQCLatticeReductionsSanity
import HeytingLean.Tests.Crypto.ConstructiveHardnessSanity
import HeytingLean.Tests.Crypto.BB84Sanity
import HeytingLean.Tests.Crypto.BB84ErrorRateSanity
import HeytingLean.Tests.Crypto.BB84MultiRoundSanity
import HeytingLean.Tests.Crypto.E91Sanity
import HeytingLean.Tests.Crypto.E91DISanity
import HeytingLean.Tests.Crypto.PQCLatticeNTTCorrectnessSanity
import HeytingLean.Tests.Crypto.PQCLatticeKPKESanity
import HeytingLean.Tests.Crypto.PQCLatticeNTTIterativeSanity
import HeytingLean.Tests.Crypto.PQCLatticeKPKECompressedSanity
import HeytingLean.Tests.Crypto.PQCLatticeCompressBoundsSanity
import HeytingLean.Tests.Crypto.PQCLatticeFailureAxiomExportSanity
import HeytingLean.Tests.Crypto.PQCLatticeFailureToySanity
import HeytingLean.Tests.Crypto.PQCLatticeFailureModelSanity
import HeytingLean.Tests.Crypto.PQCLatticeResidualAccurateSanity
import HeytingLean.Tests.Crypto.PQCLatticeNTTBridgeSanity
import HeytingLean.Tests.Crypto.PQCLatticeNTTBridgeProofSanity
import HeytingLean.Tests.Crypto.PQCGamesSanity
import HeytingLean.Tests.Crypto.PQCDSASpecSanity
import HeytingLean.Tests.Crypto.VerifiedPQCSanity
import HeytingLean.Tests.Crypto.IPAInstanceSanity
import HeytingLean.Tests.Crypto.NECPSanity
import HeytingLean.Tests.Crypto.Information.InfoTheorySanity
import HeytingLean.Tests.Crypto.Quantum.BellSanity
import HeytingLean.Tests.Crypto.Quantum.ContextualitySanity
import HeytingLean.Tests.Crypto.HybridSanity
import HeytingLean.Tests.Crypto.BB84Sanity
import HeytingLean.Tests.Crypto.E91Sanity
import HeytingLean.Tests.Crypto.CTBridgeSanity
import HeytingLean.Tests.Crypto.QECSanity

/-!
# Crypto sanity umbrella

This module groups the lightweight compile-time “sanity” checks around the PQC lattice bridge
and its spec connections.
-/

namespace HeytingLean.Tests.Crypto.AllSanity

-- Intentionally empty: importing the modules is the test.

end HeytingLean.Tests.Crypto.AllSanity
