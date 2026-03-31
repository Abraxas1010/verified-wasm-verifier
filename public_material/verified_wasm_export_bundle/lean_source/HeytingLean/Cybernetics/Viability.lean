import HeytingLean.LoF.Nucleus
import HeytingLean.Cybernetics.Observer
import HeytingLean.Cybernetics.Feedback

/-
Second-Order Cybernetics: Viability and invariance under a Reentry nucleus.
-/

namespace HeytingLean
namespace Cybernetics

open HeytingLean.LoF

universe u

variable {α : Type u} [PrimaryAlgebra α]

@[simp] def Viable (R : Reentry α) (P : α → Prop) : Prop :=
  ∀ s, P s → P (R s)

@[simp] def Invariant (R : Reentry α) (P : α → Prop) : Prop :=
  ∀ s, P s → R s = s

@[simp] def closedLoopStep {Sys Obs}
    (O : Observer Obs Sys) (F : Feedback Sys Obs) : Sys → Sys :=
  fun s => F.step s (O.observe s)

lemma preserves_closedLoopStep {Sys Obs}
    (O : Observer Obs Sys) (F : Feedback Sys Obs)
    (P : Sys → Prop)
    (h : ∀ s, P s → P (F.step s (O.observe s))) :
    ∀ s, P s → P (closedLoopStep O F s) := by
  intro s hs
  simpa [closedLoopStep] using h s hs

end Cybernetics
end HeytingLean
