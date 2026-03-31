import HeytingLean.PerspectivalPlenum.ContextualityEngine
import HeytingLean.Crypto.ConstructiveHardness

namespace HeytingLean
namespace Tests
namespace PerspectivalPlenum

open HeytingLean.Crypto.ConstructiveHardness
open HeytingLean.PerspectivalPlenum.ContextualityEngine

example (Φ : PhysicalModality) :
    (¬ Φ.toFun
      (HeytingLean.PerspectivalPlenum.ContextualityEngine.GlobalSectionTask
        HeytingLean.Quantum.Contextuality.Triangle.X
        HeytingLean.Quantum.Contextuality.Triangle.cover
        HeytingLean.Quantum.Contextuality.Triangle.model
        (fun {C} hC => HeytingLean.Quantum.Contextuality.Triangle.coverSubX (C := C) hC))) ↔
      (¬ Φ.toFun
        (HeytingLean.Crypto.ConstructiveHardness.GlobalSectionTask
          HeytingLean.Quantum.Contextuality.Triangle.X
          HeytingLean.Quantum.Contextuality.Triangle.cover
          HeytingLean.Quantum.Contextuality.Triangle.model
          (fun {C} hC => HeytingLean.Quantum.Contextuality.Triangle.coverSubX (C := C) hC))) := by
  exact triangle_physImpossible_iff_constructiveHardness Φ

example (Φ : PhysicalModality) :
    ¬ Φ.toFun
      (HeytingLean.PerspectivalPlenum.ContextualityEngine.GlobalSectionTask
        HeytingLean.Quantum.Contextuality.Triangle.X
        HeytingLean.Quantum.Contextuality.Triangle.cover
        HeytingLean.Quantum.Contextuality.Triangle.model
        (fun {C} hC => HeytingLean.Quantum.Contextuality.Triangle.coverSubX (C := C) hC)) := by
  exact globallyObstructed_implies_physImpossible
    (Φ := Φ)
    (X := HeytingLean.Quantum.Contextuality.Triangle.X)
    (cover := HeytingLean.Quantum.Contextuality.Triangle.cover)
    (e := HeytingLean.Quantum.Contextuality.Triangle.model)
    (coverSubX := fun {C} hC => HeytingLean.Quantum.Contextuality.Triangle.coverSubX (C := C) hC)
    HeytingLean.Quantum.Contextuality.Triangle.noGlobal

end PerspectivalPlenum
end Tests
end HeytingLean
