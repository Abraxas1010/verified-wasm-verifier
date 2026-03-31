import HeytingLean.Crypto.Commit.IPAInstance
import HeytingLean.NucleusDB.Commitment.Adapter
import HeytingLean.NucleusDB.Commitment.VectorModel

namespace HeytingLean.Tests.Crypto.IPAInstanceSanity

open HeytingLean.Crypto.Commit.IPAInstance
open HeytingLean.Crypto.Commit.PedersenAssumptions
open HeytingLean.Crypto.Commit.Spec
open HeytingLean.NucleusDB.Commitment

def demoAdapter2 : VCAdapter where
  scheme := scheme (demoParams 2)

def sampleRand : Int :=
  7

def sampleVector : Fin 2 → Int
  | ⟨0, _⟩ => 11
  | ⟨1, _⟩ => -3

def sampleCommitted : CommittedVector demoAdapter2 where
  vector := sampleVector
  randomness := sampleRand
  commitment := demoAdapter2.scheme.commit sampleVector sampleRand
  commitmentEq := rfl

def i1 : Fin 2 := ⟨1, by decide⟩

def π1 : demoAdapter2.scheme.Proof :=
  demoAdapter2.scheme.openAt sampleCommitted.vector sampleCommitted.randomness i1

example : VCAdapter.openingHolds demoAdapter2 sampleVector sampleRand ⟨0, by decide⟩ := by
  exact VCAdapter.openingHolds_of_openCorrect
    demoAdapter2 (demo_openCorrect 2) sampleVector sampleRand ⟨0, by decide⟩

example : sampleVector i1 = (-3 : Int) := by
  rfl

example : demoAdapter2.scheme.commit sampleVector sampleRand = (sampleVector, sampleRand) := by
  simpa [demoAdapter2, sampleRand] using demo_commit_coordinates sampleVector sampleRand

example : Vec.Scheme.VerificationConsistencyAt demoAdapter2.scheme := by
  simpa [demoAdapter2] using demo_verificationConsistencyAt 2

def toyDLogWitness :
    HeytingLean.Crypto.Commit.PedersenAssumptions.DLogHardnessWitness (demoParams 2) where
  ε := 1
  ε_nonneg := by norm_num
  sound := by
    intro A
    exact A.advantage_le_one

def toyDLogHardness : HeytingLean.Crypto.Commit.IPAInstance.DLogHardness (demoParams 2) :=
  ⟨toyDLogWitness⟩

def toyReduction :
    HeytingLean.Crypto.Commit.PedersenAssumptions.DLogReductionStatement (demoParams 2) 2 where
  loss := 0
  loss_nonneg := by norm_num
  transport := by
    intro A
    refine ⟨{
      advantage := A.advantage
      advantage_nonneg := A.advantage_nonneg
      advantage_le_one := A.advantage_le_one
    }, ?_⟩
    simp [HeytingLean.Crypto.Commit.PedersenAssumptions.HidingAdvantage,
      HeytingLean.Crypto.Commit.PedersenAssumptions.DLogAdvantage]

def toyReductionStatement :
    HeytingLean.Crypto.Commit.IPAInstance.DLogReductionStatement (demoParams 2) :=
  ⟨toyReduction⟩

example : ComputationalHiding (demoParams 2) := by
  exact computationalHiding_of_dlogReduction (demoParams 2) toyDLogHardness toyReductionStatement

example : (securityProps (demoParams 2)).computationalHidingAt := by
  exact computationalHiding_field_of_dlogReduction
    (demoParams 2) toyDLogHardness toyReductionStatement

example : ¬ (demoSecurityProps 2).computationalHidingAt := by
  simp [demoSecurityProps]

example : AuthenticatedAt demoAdapter2 sampleCommitted i1 (-3 : Int) π1 := by
  have h :
      demoAdapter2.scheme.verifyAt
        (demoAdapter2.scheme.commit sampleCommitted.vector sampleCommitted.randomness)
        i1 (sampleCommitted.vector i1) π1 :=
    VCAdapter.openingHolds_of_openCorrect
      demoAdapter2 (demo_openCorrect 2) sampleCommitted.vector sampleCommitted.randomness i1
  simpa [AuthenticatedAt, sampleCommitted, sampleVector, sampleRand, i1, π1] using h

example :
    sampleCommitted.vector i1 = (-3 : Int) := by
  rfl

example : sampleCommitted.vector i1 = (-3 : Int) := by
  have hUnique :
      sampleCommitted.vector i1 = (-3 : Int) :=
    authenticated_value_unique demoAdapter2 (demo_openSound 2)
      sampleCommitted i1 (-3 : Int) π1
      (by
        have h :
            demoAdapter2.scheme.verifyAt
              (demoAdapter2.scheme.commit sampleCommitted.vector sampleCommitted.randomness)
              i1 (sampleCommitted.vector i1) π1 :=
          VCAdapter.openingHolds_of_openCorrect
            demoAdapter2 (demo_openCorrect 2) sampleCommitted.vector sampleCommitted.randomness i1
        simpa [AuthenticatedAt, sampleCommitted, sampleVector, sampleRand, i1, π1] using h)
  simp [sampleCommitted, sampleVector, i1] at hUnique ⊢

end HeytingLean.Tests.Crypto.IPAInstanceSanity
