import HeytingLean.LoF.Combinators.Topos.SheafNeuralNet

/-!
Smoke checks for `LoF.Combinators.Topos.SheafNeuralNet`.

This validates that the sheaf Laplacian and first-order diffusion hooks are
non-placeholder and computable in a tiny one-vertex/one-edge model.
-/

namespace HeytingLean
namespace Tests
namespace Topos

open HeytingLean.LoF.Combinators.Topos

noncomputable def unitSheaf : CellularSheaf Unit Unit :=
  { stalk := fun _ => ℝ
    edge_map := fun _ => ((), ())
    restriction := fun _ => LinearMap.id }

noncomputable def oneSection : Section unitSheaf := fun _ => (1 : ℝ)

example : sheafDiffusion unitSheaf oneSection 0 = oneSection := by
  simpa using sheaf_diffusion_converges (sheaf := unitSheaf) (initial := oneSection)

example : sheafLaplacian unitSheaf oneSection () = (1 : ℝ) := by
  simp [sheafLaplacian, edgeContribution, unitSheaf, oneSection]

end Topos
end Tests
end HeytingLean
