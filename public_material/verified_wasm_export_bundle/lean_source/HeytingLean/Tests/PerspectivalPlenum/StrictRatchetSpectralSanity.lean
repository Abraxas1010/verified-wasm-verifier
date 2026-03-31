import HeytingLean.PerspectivalPlenum.StrictRatchet
import HeytingLean.PerspectivalPlenum.ProjectionObligations

namespace HeytingLean
namespace Tests
namespace PerspectivalPlenum

open HeytingLean.PerspectivalPlenum
open HeytingLean.PerspectivalPlenum.StrictRatchet
open HeytingLean.PerspectivalPlenum.StrictRatchet.Spectral
open HeytingLean.PerspectivalPlenum.ProjectionObligations

universe u

variable {α : Type u} [Order.Frame α]
variable (J : Nucleus α) (S : RatchetStep α) (steps : List (RatchetStep α))

#check Page
#check birthdayFiltration
#check pageWitness
#check d1Nontrivial
#check strictSpectralTheorem
#check dischargeHintRegistry

example :
    pageWitness .Einfty .L2 ∧ ¬ pageWitness .Einfty .L1 := by
  exact convergenceWitness_holds

example : strictSpectralTheorem := by
  exact strictSpectralTheorem_holds

example :
    ContextualityEngine.HasCechH1
      Quantum.Contextuality.Triangle.X
      Quantum.Contextuality.Triangle.cover
      Quantum.Contextuality.Triangle.model
      (fun {C} hC => Quantum.Contextuality.Triangle.coverSubX (C := C) hC) := by
  exact triangle_cech_h1_hook

example :
    Lens.CollapseToBottom Lens.Examples.euclideanLens Lens.Examples.ShapeObject.squareCircle ∧
      Lens.LocallySatisfiable Lens.Examples.higherDimLens Lens.Examples.ShapeObject.squareCircle := by
  exact square_circle_lens_relative_hook

end PerspectivalPlenum
end Tests
end HeytingLean
