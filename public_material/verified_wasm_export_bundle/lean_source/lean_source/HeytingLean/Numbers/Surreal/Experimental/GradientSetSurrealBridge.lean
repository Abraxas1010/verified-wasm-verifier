import HeytingLean.Numbers.Surreal.Experimental.NoneistLoss
import HeytingLean.Experiments.EulerSheafSurreal.Kernel

/-!
# Gradient set/surreal bridge for Noneist loss

This module connects the depth-10 Euler/Set/Surreal kernel to an existing
Noneist proof lane (`boundaryLoss_actual_le_counterfactual`) by introducing
an explicit finite gradient-selection operator on projected births.

It proves a local descent guarantee for mapped actual loss and re-establishes
actual-vs-counterfactual ordering after the gradient map.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace Experimental

open HeytingLean.Experiments.EulerSheafSurreal

/-- Mapped loss on projected births. -/
def mappedBirthLoss (goal birth : Nat) : Nat :=
  birthError birth goal

/-- Two-way finite argmin by mapped loss. -/
def chooseBetter (goal a b : Nat) : Nat :=
  if mappedBirthLoss goal a ≤ mappedBirthLoss goal b then a else b

/-- Three-way finite argmin by mapped loss. -/
def chooseBest3 (goal a b c : Nat) : Nat :=
  chooseBetter goal (chooseBetter goal a b) c

lemma chooseBetter_loss_le_left (goal a b : Nat) :
    mappedBirthLoss goal (chooseBetter goal a b) ≤ mappedBirthLoss goal a := by
  unfold chooseBetter
  by_cases h : mappedBirthLoss goal a ≤ mappedBirthLoss goal b
  · simp [h]
  · simp [h]
    exact Nat.le_of_lt (Nat.lt_of_not_ge h)

lemma chooseBetter_loss_le_right (goal a b : Nat) :
    mappedBirthLoss goal (chooseBetter goal a b) ≤ mappedBirthLoss goal b := by
  unfold chooseBetter
  by_cases h : mappedBirthLoss goal a ≤ mappedBirthLoss goal b
  · simp [h]
  · simp [h]

lemma chooseBest3_loss_le_first (goal a b c : Nat) :
    mappedBirthLoss goal (chooseBest3 goal a b c) ≤ mappedBirthLoss goal a := by
  unfold chooseBest3
  have hOuter :
      mappedBirthLoss goal (chooseBetter goal (chooseBetter goal a b) c)
        ≤ mappedBirthLoss goal (chooseBetter goal a b) :=
    chooseBetter_loss_le_left goal (chooseBetter goal a b) c
  have hInner : mappedBirthLoss goal (chooseBetter goal a b) ≤ mappedBirthLoss goal a :=
    chooseBetter_loss_le_left goal a b
  exact Nat.le_trans hOuter hInner

/-- Project target birthday to the depth-10 set/surreal lane. -/
def mappedGoalBirth (target : LossTarget) : Nat :=
  projectDepth10 target.goalBirth

/-- Project prediction birthday to the depth-10 set/surreal lane. -/
def mappedCurrentBirth (pred : AttentionToken) : Nat :=
  projectDepth10 pred.core.birth

/-- One gradient-style mapped update over projected set/surreal births. -/
def mappedGradientBirth (target : LossTarget) (pred : AttentionToken) : Nat :=
  let cur := mappedCurrentBirth pred
  chooseBest3 (mappedGoalBirth target)
    cur
    (eulerShiftDepth10 cur)
    (complementDepth10 cur)

/-- Local descent guarantee for mapped actual loss. -/
theorem mappedGradientBirth_descent (target : LossTarget) (pred : AttentionToken) :
    mappedBirthLoss (mappedGoalBirth target) (mappedGradientBirth target pred)
      ≤ mappedBirthLoss (mappedGoalBirth target) (mappedCurrentBirth pred) := by
  unfold mappedGradientBirth
  simp [chooseBest3_loss_le_first]

/-- Boundary-style loss at a fixed projected birth. -/
def mappedBoundaryLossAtBirth (mode : LossMode) (goal birth velocity : Nat) : Nat :=
  mappedBirthLoss goal birth +
    match mode with
    | .actual => 0
    | .counterfactual => velocity

/-- Existing system theorem, re-exposed as the selected in-system proof target. -/
theorem system_boundary_actual_le_counterfactual (goal : Nat) (pred : AttentionToken) :
    boundaryLoss ⟨.actual, goal⟩ pred ≤ boundaryLoss ⟨.counterfactual, goal⟩ pred :=
  boundaryLoss_actual_le_counterfactual goal pred

/-- Gradient-mapped analog of the same ordering theorem. -/
theorem mappedGradient_actual_le_counterfactual (goal : Nat) (pred : AttentionToken) :
    mappedBoundaryLossAtBirth .actual
      (projectDepth10 goal)
      (mappedGradientBirth ⟨.actual, goal⟩ pred)
      pred.velocity
      ≤
    mappedBoundaryLossAtBirth .counterfactual
      (projectDepth10 goal)
      (mappedGradientBirth ⟨.actual, goal⟩ pred)
      pred.velocity := by
  simp [mappedBoundaryLossAtBirth]

/-- Combined statement: system proof + gradient-mapped proof in one theorem. -/
theorem system_and_mapped_gradient_boundary_order (goal : Nat) (pred : AttentionToken) :
    boundaryLoss ⟨.actual, goal⟩ pred ≤ boundaryLoss ⟨.counterfactual, goal⟩ pred ∧
    mappedBoundaryLossAtBirth .actual
      (projectDepth10 goal)
      (mappedGradientBirth ⟨.actual, goal⟩ pred)
      pred.velocity
      ≤
    mappedBoundaryLossAtBirth .counterfactual
      (projectDepth10 goal)
      (mappedGradientBirth ⟨.actual, goal⟩ pred)
      pred.velocity := by
  exact ⟨
    system_boundary_actual_le_counterfactual goal pred,
    mappedGradient_actual_le_counterfactual goal pred
  ⟩

end Experimental
end Surreal
end Numbers
end HeytingLean
