import HeytingLean.Noneism.Semantics.RoutleyMeyer

/-!
# Surreal.ParaconsistentModal

SN-013 baseline: a concrete Routley-Meyer countermodel witnessing non-explosion.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace ParaconsistentModal

open HeytingLean.Noneism
open Formula
open HeytingLean.Noneism.RM

inductive Sym where
  | p
  | q
  deriving Repr, DecidableEq

inductive W where
  | w0
  | w1
  deriving Repr, DecidableEq

inductive D where
  | d0
  deriving Repr, DecidableEq

def frame : Frame W where
  star
    | .w0 => .w1
    | .w1 => .w0
  R := fun _ _ _ => True

def model : Model Sym W D where
  F := frame
  interp := fun w s _ =>
    match w, s with
    | .w0, .p => True
    | .w1, .p => False
    | _, .q => False
  existsP := fun _ _ => True

def ρ : Valuation D := fun _ => .d0

def φp : Formula Sym := .pred .p []
def φq : Formula Sym := .pred .q []

@[simp] theorem sat_p_w0 : sat model ρ .w0 φp := by
  simp [sat, model, φp]

@[simp] theorem sat_not_p_w0 : sat model ρ .w0 (.not φp) := by
  simp [sat, model, frame, φp]

@[simp] theorem not_sat_q_w0 : ¬ sat model ρ .w0 φq := by
  simp [sat, model, φq]

/-- Non-explosion witness: `p ∧ ¬p` at `w0`, while `q` still fails at `w0`. -/
theorem non_explosion_witness :
    sat model ρ .w0 (.and φp (.not φp)) ∧ ¬ sat model ρ .w0 φq := by
  refine ⟨?_, ?_⟩
  · simp [sat, model, frame, φp]
  · exact not_sat_q_w0

/-- `p ∧ ¬p → q` is not valid at `w0` in this RM model. -/
theorem explosion_implication_fails :
    ¬ sat model ρ .w0 (.imp (.and φp (.not φp)) φq) := by
  intro h
  have hpand : sat model ρ .w0 (.and φp (.not φp)) := by
    simp [sat, model, frame, φp]
  have hq : sat model ρ .w0 φq := h .w0 .w0 trivial hpand
  exact (not_sat_q_w0 hq)

end ParaconsistentModal
end Surreal
end Numbers
end HeytingLean
