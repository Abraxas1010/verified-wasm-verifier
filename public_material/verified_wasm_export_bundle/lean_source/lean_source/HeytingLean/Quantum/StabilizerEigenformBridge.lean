import HeytingLean.Quantum.StabilizerNucleus
import HeytingLean.LoF.Bauer.Eigenforms

/-!
# Quantum.StabilizerEigenformBridge

Bridge theorem: the stabilizer closure operator `U ↦ U ∪ codeSpace` is the Bauer
`joinConst codeSpace` endomap on `Set α`, so its least fixed point is `codeSpace`.
-/

namespace HeytingLean
namespace Quantum
namespace StabilizerEigenformBridge

open StabilizerCode
open LoF.Bauer.Eigenforms
open LoF.Bauer.FixedPoint

universe u v

variable {α : Type u} {C : StabilizerCode.{u, v} α}

@[simp] theorem stabilizerNucleus_apply_eq_joinConst (U : Set α) :
    StabilizerNucleus.stabilizerNucleus (α := α) C U =
      joinConst (D := Set α) C.codeSpace U := by
  simp [StabilizerNucleus.stabilizerNucleus_apply, joinConst]

theorem stabilizer_nucleus_is_bauer_eigenform :
    lfp (D := Set α)
      (joinConst (D := Set α) C.codeSpace)
      (joinConst_ωcontinuous (D := Set α) C.codeSpace)
      = C.codeSpace := by
  simpa using (lfp_joinConst_eq (D := Set α) (p := C.codeSpace))

end StabilizerEigenformBridge
end Quantum
end HeytingLean
