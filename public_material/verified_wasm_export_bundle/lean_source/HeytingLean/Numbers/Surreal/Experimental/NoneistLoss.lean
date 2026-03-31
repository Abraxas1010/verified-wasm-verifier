import HeytingLean.Numbers.Surreal.Experimental.NoneistNeural

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace Experimental

/-- Target mode for boundary-aware loss evaluation. -/
inductive LossMode where
  | actual
  | counterfactual
  deriving Repr, DecidableEq

/-- Loss target for the Noneist loss lane. -/
structure LossTarget where
  mode : LossMode
  goalBirth : Nat
  deriving Repr, DecidableEq

/-- Counterfactual mode receives explicit velocity penalty. -/
def modePenalty (mode : LossMode) (pred : AttentionToken) : Nat :=
  match mode with
  | .actual => 0
  | .counterfactual => pred.velocity

/-- Absolute birthday error used by loss terms. -/
def birthError (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

/-- Boundary-aware loss for contradictory/Noneist targets. -/
def boundaryLoss (target : LossTarget) (pred : AttentionToken) : Nat :=
  birthError pred.core.birth target.goalBirth + modePenalty target.mode pred

theorem boundaryLoss_nonnegative (target : LossTarget) (pred : AttentionToken) :
    0 ≤ boundaryLoss target pred := by
  exact Nat.zero_le _

theorem boundaryLoss_le_error_plus_velocity (target : LossTarget) (pred : AttentionToken) :
    boundaryLoss target pred ≤ birthError pred.core.birth target.goalBirth + pred.velocity := by
  cases target with
  | mk mode goal =>
      cases mode <;> simp [boundaryLoss, modePenalty]

theorem boundaryLoss_actual_le_counterfactual (goal : Nat) (pred : AttentionToken) :
    boundaryLoss ⟨.actual, goal⟩ pred ≤ boundaryLoss ⟨.counterfactual, goal⟩ pred := by
  simp [boundaryLoss, modePenalty]

theorem counterfactual_loss_strict_of_positive_velocity
    (goal : Nat) (pred : AttentionToken) (hVel : 0 < pred.velocity) :
    boundaryLoss ⟨.actual, goal⟩ pred < boundaryLoss ⟨.counterfactual, goal⟩ pred := by
  have hStrict :
      birthError pred.core.birth goal <
        birthError pred.core.birth goal + pred.velocity :=
    Nat.lt_add_of_pos_right hVel
  simpa [boundaryLoss, modePenalty] using hStrict

/-- Combined loss for paradox-like dual targets (actual + counterfactual). -/
def paradoxPairLoss (goal : Nat) (pred : AttentionToken) : Nat :=
  boundaryLoss ⟨.actual, goal⟩ pred + boundaryLoss ⟨.counterfactual, goal⟩ pred

theorem paradoxPairLoss_closed_form (goal : Nat) (pred : AttentionToken) :
    paradoxPairLoss goal pred =
      birthError pred.core.birth goal + birthError pred.core.birth goal + pred.velocity := by
  simp [paradoxPairLoss, boundaryLoss, modePenalty, Nat.add_assoc]

/-- Counterfactual contribution guarantees non-collapse in paradox pair loss. -/
theorem paradoxPairLoss_ge_actual (goal : Nat) (pred : AttentionToken) :
    boundaryLoss ⟨.actual, goal⟩ pred ≤ paradoxPairLoss goal pred := by
  simp [paradoxPairLoss, boundaryLoss]

end Experimental
end Surreal
end Numbers
end HeytingLean
