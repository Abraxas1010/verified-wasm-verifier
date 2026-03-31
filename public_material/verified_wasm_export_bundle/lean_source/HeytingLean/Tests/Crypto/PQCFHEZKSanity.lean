import HeytingLean.Crypto.FHE.NoiseHomomorphicSpec
import HeytingLean.Crypto.Lattice.NoiseMLWE
import HeytingLean.Crypto.ZK.SISPoKDemo
import HeytingLean.Crypto.ZK.SigmaProtocolSpec

namespace HeytingLean
namespace Tests
namespace Crypto
namespace PQCFHEZKSanity

open HeytingLean.Crypto.Lattice
open HeytingLean.Crypto.FHE
open HeytingLean.Crypto.ZK

#check EncRel
#check addCt
#check homAdd_correct
#check homAddMul_left_correct
#check homAddMul_right_correct
#check PoK
#check SigmaProtocol
#check SISRel

def toyMLWE : MLWEParams :=
  { n := 1, q := 17, k := 1 }

noncomputable def toyS1 : ModVec toyMLWE.k toyMLWE.n toyMLWE.q :=
  fun _i => fun _j => 1

noncomputable def toyS2 : ModVec toyMLWE.k toyMLWE.n toyMLWE.q :=
  fun _i => fun _j => 2

noncomputable def toyM : ModVec toyMLWE.k toyMLWE.n toyMLWE.q :=
  0

noncomputable def toyCt1 : MLWEInstance toyMLWE :=
  { A := 1, b := toyS1 }

noncomputable def toyCt2 : MLWEInstance toyMLWE :=
  { A := 1, b := toyS2 }

example : EncRel toyMLWE 0 toyCt1 toyM := by
  refine ⟨toyS1, 0, boundedNatRep_zero toyMLWE 0, ?_⟩
  simp [toyCt1, toyM]

example : EncRel toyMLWE 0 toyCt2 toyM := by
  refine ⟨toyS2, 0, boundedNatRep_zero toyMLWE 0, ?_⟩
  simp [toyCt2, toyM]

example :
    EncRel toyMLWE (0 + 0) (addCt toyMLWE toyCt1 toyCt2) (toyM + toyM) := by
  refine homAdd_correct (P := toyMLWE) (ct1 := toyCt1) (ct2 := toyCt2) (m1 := toyM) (m2 := toyM) ?_ ?_ ?_
  · rfl
  · exact (by
      refine ⟨toyS1, 0, boundedNatRep_zero toyMLWE 0, ?_⟩
      simp [toyCt1, toyM])
  · exact (by
      refine ⟨toyS2, 0, boundedNatRep_zero toyMLWE 0, ?_⟩
      simp [toyCt2, toyM])

example :
    ∃ w : ZVec toyParams.n toyParams.q, (SISRel toyParams 0).holds toyStmt w := by
  have hverify :
      (sisPoK toyParams 0).verify toyStmt (0 : ZVec toyParams.n toyParams.q) = true := by
    simp [sisPoK, sisVerify, vecEqZeroCheck, shortNatRepCheck, toyStmt]
  exact (sisPoK toyParams 0).sound toyStmt (0 : ZVec toyParams.n toyParams.q) hverify

-- Sigma protocol toy: response carries witness.
def toyRel : Relation Nat Nat :=
  { holds := fun s w => s = w + 1 }

instance : ∀ s w : Nat, Decidable (toyRel.holds s w) := by
  intro s w
  dsimp [toyRel, Relation.holds]
  infer_instance

example :
    (witnessSigma toyRel).verify 5 ((witnessSigma toyRel).commit 5 4 ()) false
        ((witnessSigma toyRel).respond 5 4 () false) = true := by
  simpa using (witnessSigma toyRel).complete (s := 5) (w := 4) (by decide : toyRel.holds 5 4) () false

end PQCFHEZKSanity
end Crypto
end Tests
end HeytingLean
