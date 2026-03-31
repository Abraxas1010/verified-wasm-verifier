import HeytingLean.Crypto.ZK.PlonkIR
import HeytingLean.Crypto.ZK.R1CS

namespace HeytingLean
namespace Crypto
namespace Tests

open ZK
open ZK.Plonk

/-- Simple non-identity permutation test for PLONK renaming equivalence.
    We use σ that swaps 0 and 1, and an assignment `a` with a 0 = a 1, so
    `a` agrees with `a ∘ σ` on the support of the system. -/
theorem plonk_native_iff_renamed_swap :
    let σ : ZK.Var → ZK.Var := fun v => if v = 0 then 1 else if v = 1 then 0 else v
    -- trivial system with two tautological gates touching vars 0 and 1
    let g0 : Gate := { A := R1CS.LinComb.single 0 1, C := R1CS.LinComb.single 0 1 }
    let g1 : Gate := { A := R1CS.LinComb.single 1 1, C := R1CS.LinComb.single 1 1 }
    let sys : System := { gates := [g0, g1], copyPermutation := [1, 0] }
    let a : ZK.Var → ℚ := fun _ => 0
    sys.satisfiedNative a ↔ (System.toR1CS sys).satisfied a := by
  classical
  intros σ g0 g1 sys a
  -- The copy system is satisfied under a constant assignment
  have hCopy : (copyConstraintSystem sys.copyPermutation).satisfied a := by
    intro c hc; 
    -- each equality `a i = a j` holds under a constant assignment
    rcases List.mem_map.1 hc with ⟨ij, hij, rfl⟩
    rcases ij with ⟨i, j⟩; 
    simp [ZK.Constraint.satisfied, eqVarConstraint, a, ZK.LinComb.eval_single, ZK.LinComb.eval_ofConst]
  -- Apply the copy-satisfied equivalence
  exact satisfiedNative_iff_r1cs_of_copySatisfied (sys := sys) (a := a) hCopy

end Tests
end Crypto
end HeytingLean
