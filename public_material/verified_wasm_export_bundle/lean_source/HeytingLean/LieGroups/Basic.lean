import HeytingLean.LieGroups.Imports

set_option autoImplicit false

open scoped Manifold

namespace HeytingLean
namespace LieGroups

section Basic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners 𝕜 E H)

variable (n : WithTop ℕ∞)

variable (G : Type*) [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- Utility alias: the Lie algebra of a Lie group `G` is `GroupLieAlgebra I G`. -/
abbrev 𝔤 (I : ModelWithCorners 𝕜 E H) (G : Type*) [TopologicalSpace G] [ChartedSpace H G]
    [Group G] :=
  GroupLieAlgebra I G

/-- Re-export: inversion is `C^n` in a Lie group. -/
lemma contMDiff_inv [LieGroup I n G] :
    ContMDiff I I n (fun g : G => g⁻¹) :=
  LieGroup.contMDiff_inv

/-- Re-export: multiplication is `C^n` in a Lie group. -/
lemma contMDiff_mul [LieGroup I n G] :
    ContMDiff (I.prod I) I n (fun p : G × G => p.1 * p.2) :=
  ContMDiffMul.contMDiff_mul

section GroupLieAlgebra

variable [CompleteSpace E]
variable [LieGroup I n G]
variable [Fact (minSmoothness 𝕜 3 ≤ n)]

-- Make the `minSmoothness` Lie group instance available for Mathlib's Lie bracket construction.
private lemma lieGroup_minSmoothness :
    LieGroup I (minSmoothness 𝕜 3) G :=
  LieGroup.of_le (I := I) (G := G) (m := minSmoothness 𝕜 3) (n := n)
    (by simpa using (inferInstance : Fact (minSmoothness 𝕜 3 ≤ n)).out)

attribute [local instance] lieGroup_minSmoothness

/-- `GroupLieAlgebra I G` is a Lie ring (under the standard smoothness/completeness hypotheses). -/
example : LieRing (GroupLieAlgebra I G) := by
  infer_instance

/-- `GroupLieAlgebra I G` is a Lie algebra over `𝕜`. -/
example : LieAlgebra 𝕜 (GroupLieAlgebra I G) := by
  infer_instance

end GroupLieAlgebra

end Basic

end LieGroups
end HeytingLean
