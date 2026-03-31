import HeytingLean.Quantum.Contextuality.Witness

/-!
# Triangle contextuality witness (re-export)

Re-exports the triangle no-global-section witness from
`HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel`.
-/

namespace HeytingLean
namespace Quantum
namespace Contextuality
namespace Triangle

open HeytingLean.LoF.CryptoSheaf.Quantum

abbrev X := HeytingLean.LoF.CryptoSheaf.Quantum.X_abc
abbrev cover := HeytingLean.LoF.CryptoSheaf.Quantum.triangleCover
abbrev model := HeytingLean.LoF.CryptoSheaf.Quantum.triangleModel

abbrev coverSubX :
    ∀ {C : Context}, C ∈ cover → C ⊆ X :=
  fun {_} hC => HeytingLean.LoF.CryptoSheaf.Quantum.triangle_cover_subset_X hC

theorem noGlobal :
    NoGlobalSection X cover model (fun {C} hC => coverSubX (C := C) hC) := by
  simpa [X, cover, model, coverSubX] using
    (HeytingLean.LoF.CryptoSheaf.Quantum.triangle_no_global)

/-- The triangle contextuality witness as packaged data. -/
def witness : Witness where
  X := X
  cover := cover
  e := model
  coverSubX := fun {C} hC => coverSubX (C := C) hC
  noGlobal := noGlobal

end Triangle
end Contextuality
end Quantum
end HeytingLean
