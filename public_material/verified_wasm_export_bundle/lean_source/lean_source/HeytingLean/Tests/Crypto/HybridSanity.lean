import HeytingLean.Crypto.Hybrid.QKDPQHybrid

namespace HeytingLean.Tests.Crypto

open HeytingLean
open HeytingLean.Crypto

namespace HybridSanity

open Crypto.Composable

#check Crypto.Hybrid.QKDExtractionWitness
#check Crypto.Hybrid.WitnessedHybridKEM
#check Crypto.Hybrid.HybridKEM.withQKDExtractionWitness
#check Crypto.Hybrid.WitnessedHybridKEM.qkd_statDistance_le_epsilonSec
#check Crypto.Hybrid.WitnessedHybridKEM.qkd_correctness_plus_extraction_le_total

def keProtocol (n : Nat) : Composable.Protocol (Composable.Instances.IdealKeyExchange n) where
  State := Unit
  Message := Unit
  init := ()
  execute := fun _i _s => (fun _ => false, (), ())

def keSim (n : Nat) : Composable.Simulator (Composable.Instances.IdealKeyExchange n) (keProtocol n) where
  SimState := Unit
  init := ()
  simulate := fun _leak _s => ((), ())

theorem ke_uc_secure (n : Nat) :
    Composable.UCSecure (Composable.Instances.IdealKeyExchange n) (keProtocol n) := by
  refine ⟨keSim n, (fun f g => f = g), ?_⟩
  rfl

noncomputable def toyKEM : Crypto.KEM.KEMScheme where
  PublicKey := Unit
  SecretKey := Unit
  Ciphertext := Unit
  SharedSecret := Bool
  keygen := PMF.pure ((), ())
  encaps := fun _ => PMF.pure ((), false)
  decaps := fun _ _ => some false

noncomputable def toyAdversary : Crypto.KEM.INDCCAAdversary toyKEM where
  run := fun _pk _ctStar _ss _oracle => PMF.pure true

noncomputable def toyAdvantage : ℝ :=
  Crypto.KEM.IND_CCA_Advantage toyKEM toyAdversary

example : 0 ≤ toyAdvantage := by
  have h :
      0 ≤ |Games.INDCCA.winProb (K := Crypto.KEM.toGameKEM toyKEM) (A := toyAdversary) true -
        Games.INDCCA.winProb (K := Crypto.KEM.toGameKEM toyKEM) (A := toyAdversary) false| :=
    abs_nonneg _
  simp [toyAdvantage, Crypto.KEM.IND_CCA_Advantage, Games.INDCCA.advantage] at h ⊢

example :
    Crypto.Hybrid.HybridSecure (πqkd := keProtocol 8) toyKEM := by
  left
  exact ke_uc_secure 8

example
    (hLeft : Crypto.KEM.LeftReductionStatement toyKEM toyKEM)
    (hRight : Crypto.KEM.RightReductionStatement toyKEM toyKEM)
    (hSec : Crypto.KEM.IND_CCA toyKEM) :
    Crypto.KEM.IND_CCA (Crypto.KEM.hybridKEM toyKEM toyKEM) := by
  let bundle : Crypto.KEM.ReductionAssumptionBundle toyKEM toyKEM :=
    { left := hLeft, right := hRight }
  exact Crypto.KEM.hybrid_security_of_documentedAssumptions
    toyKEM toyKEM ⟨bundle⟩ (Or.inl hSec)

end HybridSanity

end HeytingLean.Tests.Crypto
