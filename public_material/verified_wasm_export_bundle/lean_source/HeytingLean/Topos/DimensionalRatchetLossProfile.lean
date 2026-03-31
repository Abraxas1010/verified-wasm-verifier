import HeytingLean.Topos.DimensionalRatchetTranslate

namespace HeytingLean
namespace Topos
namespace DimensionalRatchet
namespace LossProfile

open HeytingLean.Quantum
open HeytingLean.Quantum.Translate
open HeytingLean.Quantum.OML

universe u v

variable {β : Type u} {α : Type v}
variable [OrthocomplementedLattice β] [OrthomodularLattice β] [CompleteLattice α]

/-- Optional strengthening not provided by `QLMap` data by default. -/
def JoinExact (T : QLMap β α) : Prop :=
  ∀ a b : β, T.tr (a ⊔ b) = T.M.close (T.tr a ⊔ T.tr b)

/-- `QLMap` always preserves meets exactly up to the modality closure equation. -/
theorem preserve_inf_exact (T : QLMap β α) (a b : β) :
    T.tr (a ⊓ b) = T.M.close (T.tr a ⊓ T.tr b) :=
  T.map_inf a b

/-- `QLMap` guarantees join preservation only as an upper-bound inequality. -/
theorem preserve_join_upper_bound (T : QLMap β α) (a b : β) :
    T.tr (a ⊔ b) ≤ T.M.close (T.tr a ⊔ T.tr b) :=
  T.tr_sup_le a b

/-- Exact join preservation is available only when supplied as an explicit extra hypothesis. -/
theorem preserve_join_exact_of_assumption
    (T : QLMap β α) (hJoin : JoinExact T) (a b : β) :
    T.tr (a ⊔ b) = T.M.close (T.tr a ⊔ T.tr b) :=
  hJoin a b

/-- Concrete, auditable matrix for what this transport lane does and does not claim unconditionally. -/
structure PreservationMatrix where
  meetExact : Bool
  joinUpperBound : Bool
  joinExactUnconditional : Bool
  sasakiToHeytingImpUnconditional : Bool
  deriving DecidableEq, Repr

/-- Base matrix for any `QLMap` lane before extra assumptions are added. -/
def baseMatrix : PreservationMatrix :=
  { meetExact := true
    joinUpperBound := true
    joinExactUnconditional := false
    sasakiToHeytingImpUnconditional := false }

@[simp] theorem baseMatrix_join_not_unconditional :
    baseMatrix.joinExactUnconditional = false := rfl

section Sasaki

variable [HasCompl α]

/-- Sasaki-to-Heyting bridge is available after adding complement-preservation assumptions. -/
theorem sasaki_bridge_available_with_compl
    (T : QLMap β α) [QLMap.ComplPreserving T] (a b : β) :
    T.M.J (T.tr (HeytingLean.Quantum.OML.sasakiHook a b))
      ≤ T.M.J ((T.tr a)ᶜ ⊔ T.tr b) := by
  have h :=
    QLMap.sasakiHook_le_translated_nucleus_imp
      (F := T) (hCompl := inferInstance) (a := a) (b := b)
  have h' := T.M.J.monotone h
  simpa [T.M.idempotent] using h'

end Sasaki

end LossProfile
end DimensionalRatchet
end Topos
end HeytingLean
