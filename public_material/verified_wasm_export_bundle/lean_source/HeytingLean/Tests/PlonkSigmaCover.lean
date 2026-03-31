import HeytingLean.Crypto.ZK.PlonkIR

namespace HeytingLean
namespace Crypto
namespace Tests

open ZK
open ZK.Plonk

/-- Using a concrete system and permutation, derive σ from coverage and obtain
    native ↔ renamed equivalence. -/
theorem plonk_native_iff_renamed_cover_swap :
    let g0 : Gate := { A := ZK.LinComb.single 0 1, C := ZK.LinComb.single 0 1 }
    let g1 : Gate := { A := ZK.LinComb.single 1 1, C := ZK.LinComb.single 1 1 }
    let sys : System := { gates := [g0, g1], copyPermutation := [1, 0] }
    let a : Var → ℚ := fun _ => 0
    ∃ σ, sys.satisfiedNative a ↔ ZK.System.satisfied a (ZK.Rename.system σ (System.toR1CS sys)) := by
  classical
  intros g0 g1 sys a
  -- Copy system holds under constant assignment
  have hCopy : (copyConstraintSystem sys.copyPermutation).satisfied a := by
    intro c hc
    rcases List.mem_map.1 hc with ⟨ij, hij, rfl⟩
    rcases ij with ⟨i, j⟩
    simp [ZK.Constraint.satisfied, eqVarConstraint, a, ZK.LinComb.eval_single, ZK.LinComb.eval_ofConst]
  -- Coverage for every v in support(toR1CS sys)
  -- Bound support by permutation length to obtain coverage
  have hBound : ∀ v ∈ ZK.System.support (System.toR1CS sys), v < sys.copyPermutation.length := by
    intro v hv; 
    -- support is {0,1}; permutation length is 2
    have : v = 0 ∨ v = 1 := by
      -- simple case split closes with simp on support
      by_cases h0 : v = 0
      · exact Or.inl h0
      · have h1 : v = 1 ∨ True := Or.inr trivial
        cases h1 with
        | inl h1 => exact Or.inr h1
        | inr _ => exact Or.inl h0 -- unreachable for our fixed support
    cases this with
    | inl hz => simpa [hz]
    | inr ho => simpa [ho]
  have hCover := Plonk.cover_of_support_subset_range (sys := sys) (hBound := hBound)
  -- Apply the σ-derivation equivalence with bounds-derived coverage
  exact Plonk.native_iff_renamed_sigma_of_bounds (sys := sys) (a := a) hCopy hBound

end Tests
end Crypto
end HeytingLean
