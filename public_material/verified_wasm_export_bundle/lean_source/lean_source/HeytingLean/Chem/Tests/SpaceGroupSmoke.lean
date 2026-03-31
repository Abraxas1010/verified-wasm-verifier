import HeytingLean.Chem.Materials.Symmetry.SpaceGroups
import Mathlib.Tactic

/-!
# Space-group smoke tests

Compile-only checks that:
- affine operations form a group and act on fractional coordinates;
- generator-based subgroups contain their generators.
-/

namespace HeytingLean
namespace Chem
namespace Tests

open HeytingLean.Chem.Materials
open HeytingLean.Chem.Materials.Symmetry
open HeytingLean.Chem.Materials.Symmetry.Seed

example :
    translation3 (vec3 (1/2) 0 0) • vec3 0 0 0 = vec3 (1/2) 0 0 := by
  funext i
  fin_cases i <;> simp [translation3, AffineOpG.apply, vec3]

example (x : FracCoord 3) : (flipX * flipY) • x = flipX • (flipY • x) := by
  simpa using (mul_smul (flipX : AffineOpG 3) (flipY : AffineOpG 3) x)

example : (flipX : AffineOpG 3) ∈ cubicSignFlips := by
  -- `cubicSignFlips` is defined as a closure of a generator set.
  change flipX ∈ Subgroup.closure (fun g => g ∈ [flipX, flipY, flipZ])
  refine Subgroup.subset_closure ?_
  -- Reduce the `Set` membership goal to list membership.
  change flipX ∈ [flipX, flipY, flipZ]
  simp

example : (translation3 (vec3 0 (1/2) (1/2)) : AffineOpG 3) ∈ fccSeed := by
  change translation3 (vec3 0 (1/2) (1/2)) ∈
      Subgroup.closure (fun g =>
        g ∈
          [ translation3 (vec3 0 (1/2) (1/2))
          , translation3 (vec3 (1/2) 0 (1/2))
          , translation3 (vec3 (1/2) (1/2) 0)
          , flipX, flipY, flipZ
          ])
  refine Subgroup.subset_closure ?_
  change
      translation3 (vec3 0 (1/2) (1/2)) ∈
        [ translation3 (vec3 0 (1/2) (1/2))
        , translation3 (vec3 (1/2) 0 (1/2))
        , translation3 (vec3 (1/2) (1/2) 0)
        , flipX, flipY, flipZ
        ]
  simp

end Tests
end Chem
end HeytingLean
