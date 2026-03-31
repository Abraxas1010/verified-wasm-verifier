import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

import HeytingLean.Quantum.StabilizerNucleus
import HeytingLean.Quantum.StabilizerEigenformBridge

namespace HeytingLean
namespace Tests
namespace Quantum
namespace TWA

open HeytingLean.Quantum
open HeytingLean.Quantum.StabilizerCode
open HeytingLean.Quantum.StabilizerNucleus
open HeytingLean.Quantum.StabilizerEigenformBridge

/-! Compile-time sanity checks for Phase 6 (stabilizer nucleus on sets). -/

namespace StabilizerNucleusDemo

private abbrev α := Fin 4

private def C : StabilizerCode α where
  Gen := Fin 2
  good := fun
    | 0 => {0, 1}
    | 1 => {1, 2}

example : (1 : α) ∈ C.codeSpace := by
  -- `1` satisfies both constraints.
  simp [StabilizerCode.codeSpace, C]

example : (0 : α) ∉ C.codeSpace := by
  intro h0
  have h' := h0
  -- Simplifying the hypothesis produces a direct contradiction.
  simp [StabilizerCode.codeSpace, C] at h'

example (U : Set α) : stabilizerNucleus (α := α) C U = U ∪ C.codeSpace := rfl

example (U : Set α) :
    stabilizerNucleus (α := α) C U = U ↔ C.codeSpace ⊆ U := by
  exact stabilizerNucleus_fixed_iff (α := α) C U

example : ((⊥ : Core (α := α) C) : Set α) = C.codeSpace := by
  exact bot_val_eq_codeSpace (α := α) C

example : Order.Frame (Core (α := α) C) := by
  infer_instance

example :
    HeytingLean.LoF.Bauer.FixedPoint.lfp (D := Set α)
      (HeytingLean.LoF.Bauer.Eigenforms.joinConst (D := Set α) C.codeSpace)
      (HeytingLean.LoF.Bauer.Eigenforms.joinConst_ωcontinuous (D := Set α) C.codeSpace)
      = C.codeSpace := by
  simpa using (stabilizer_nucleus_is_bauer_eigenform (C := C))

end StabilizerNucleusDemo

end TWA
end Quantum
end Tests
end HeytingLean
