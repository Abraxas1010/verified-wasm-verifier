import Mathlib.Data.Fin.Basic

import HeytingLean.Analysis.SpectralHeyting

namespace HeytingLean
namespace Tests
namespace Analysis

open scoped Classical

open HeytingLean.Analysis
open HeytingLean.Analysis.SpectralNucleus

/-! Compile-time sanity checks for Phase 5 (spectral Heyting scaffolding). -/

namespace SpectralDemo

private abbrev ι := Fin 4

private def Ω : Set ι := {0}

private def R : Nucleus (Set ι) := coreClosure (ι := ι) Ω

example (U : Set ι) : R U = U ∪ Ω := by
  simp [R, SpectralNucleus.coreClosure_apply]

example : coreClosure (ι := ι) Ω Ω = Ω := by
  apply (coreClosure_fixed_iff (ι := ι) Ω Ω).2
  intro x hx
  exact hx

example (U : Set ι) :
    U ∈ (coreClosure (ι := ι) Ω).toSublocale ↔ Ω ⊆ U := by
  simpa using (mem_Core_iff_contains (ι := ι) Ω U)

example : Order.Frame (Core (ι := ι) Ω) := by
  infer_instance

end SpectralDemo

namespace FourierStatementDemo

open HeytingLean.Analysis.FourierHeyting

private def idPreserves (X : Type) [Order.Frame X] : PreservesHeyting X X :=
  { F := FrameHom.id X
    map_himp := by
      intro a b
      rfl }

example : True := by
  -- Existence check: the statement record can be instantiated.
  have _ := idPreserves (X := Set Nat)
  trivial

end FourierStatementDemo

end Analysis
end Tests
end HeytingLean

