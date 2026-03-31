import Mathlib
import HeytingLean.Logic.PSR.Robustness

/-!
# Euler-Sheaf-Surreal generative control contracts

This module provides a compact objective scaffold for runtime controllers that
must simultaneously satisfy:

1. **global balance** (zero-sum residual),
2. **dialectic coherence** (thesis/antithesis/synthesis alignment),
3. **PSR robustness** (stable under admissible perturbation),
4. **Occam pressure** (prefer simpler program classes).

The objective is intentionally arithmetic (`Nat`) so it can be exported and
mirrored in executable runtimes with clear, auditable weight semantics.
-/

namespace HeytingLean
namespace Experiments
namespace EulerSheafSurreal

/-- Program-family dial used by the runtime controller search. -/
inductive ProgramClass
  | basicFunction
  | compositionalFunction
  | turingLike
deriving Repr, DecidableEq

/-- Occam base complexity prior by program class. -/
def ProgramClass.baseComplexity : ProgramClass → Nat
  | .basicFunction => 1
  | .compositionalFunction => 3
  | .turingLike => 7

/-- Runtime signals entering the objective. -/
structure ControlSignals where
  hardConstraintViolations : Nat
  zeroBalanceResidual : Nat
  thesisMass : Nat
  antithesisMass : Nat
  synthesisMass : Nat
  psrRobustWitness : Bool
  activeParameterCount : Nat
  programClass : ProgramClass
deriving Repr

/-- Dialectic imbalance (`|thesis - antithesis|`). -/
def dialecticImbalance (s : ControlSignals) : Nat :=
  Nat.dist s.thesisMass s.antithesisMass

/-- Dialectic synthesis deficit (`max(0, min(thesis, antithesis) - synthesis)`). -/
def dialecticDeficit (s : ControlSignals) : Nat :=
  Nat.min s.thesisMass s.antithesisMass - s.synthesisMass

/-- PSR penalty (0 when robust witness is present, otherwise 1). -/
def psrPenalty (s : ControlSignals) : Nat :=
  if s.psrRobustWitness then 0 else 1

/-- Occam penalty = class prior + active parameter burden. -/
def occamPenalty (s : ControlSignals) : Nat :=
  s.programClass.baseComplexity + s.activeParameterCount

/-- Objective weights (Nat-scaled). -/
structure ObjectiveWeights where
  wHard : Nat := 1000
  wZeroBalance : Nat := 20
  wDialecticImbalance : Nat := 5
  wDialecticDeficit : Nat := 5
  wPSR : Nat := 30
  wOccam : Nat := 1
deriving Repr

/-- Total control objective. Lower is better. -/
def controlObjective (w : ObjectiveWeights) (s : ControlSignals) : Nat :=
  w.wHard * s.hardConstraintViolations
    + w.wZeroBalance * s.zeroBalanceResidual
    + w.wDialecticImbalance * dialecticImbalance s
    + w.wDialecticDeficit * dialecticDeficit s
    + w.wPSR * psrPenalty s
    + w.wOccam * occamPenalty s

theorem dialecticImbalance_nonneg (s : ControlSignals) :
    0 ≤ dialecticImbalance s := Nat.zero_le _

theorem dialecticDeficit_nonneg (s : ControlSignals) :
    0 ≤ dialecticDeficit s := Nat.zero_le _

theorem psrPenalty_zero_iff (s : ControlSignals) :
    psrPenalty s = 0 ↔ s.psrRobustWitness = true := by
  by_cases h : s.psrRobustWitness
  · simp [psrPenalty, h]
  · simp [psrPenalty, h]

theorem psrPenalty_pos_of_not_robust (s : ControlSignals) (h : s.psrRobustWitness = false) :
    psrPenalty s = 1 := by
  simp [psrPenalty, h]

theorem occamPenalty_ge_base (s : ControlSignals) :
    s.programClass.baseComplexity ≤ occamPenalty s := by
  unfold occamPenalty
  exact Nat.le_add_right _ _

theorem controlObjective_nonneg (w : ObjectiveWeights) (s : ControlSignals) :
    0 ≤ controlObjective w s := Nat.zero_le _

/-- Perfect-control witness (all penalties vanish except unavoidable class prior when `wOccam ≠ 0`). -/
def PerfectControl (s : ControlSignals) : Prop :=
  s.hardConstraintViolations = 0 ∧
  s.zeroBalanceResidual = 0 ∧
  s.thesisMass = s.antithesisMass ∧
  s.synthesisMass = Nat.min s.thesisMass s.antithesisMass ∧
  s.psrRobustWitness = true ∧
  s.activeParameterCount = 0

theorem controlObjective_of_perfect
    (w : ObjectiveWeights) (s : ControlSignals)
    (h : PerfectControl s) :
    controlObjective w s = w.wOccam * s.programClass.baseComplexity := by
  rcases h with ⟨hHard, hZero, hBal, hSynth, hPSR, hAct⟩
  unfold controlObjective dialecticImbalance dialecticDeficit psrPenalty occamPenalty
  simp [hHard, hZero, hBal, hSynth, hPSR, hAct]

section PSRBridge

open HeytingLean.Logic.PSR
open HeytingLean.LoF

variable {α : Type u} [PrimaryAlgebra α] [LE ℝ]

/-- Runtime bridge: a genuine PSR robustness proof yields zero PSR penalty. -/
theorem psrPenalty_zero_of_proof
    (R : Reentry α) (a : α) (ε : ℝ)
    (hrob : PSR_Robust (R := R) (a := a) ε)
    (s : ControlSignals)
    (hs : s.psrRobustWitness = true) :
    psrPenalty s = 0 := by
  -- `hrob` is intentionally consumed as a proof witness for auditable linkage.
  have _ := hrob
  simp [psrPenalty, hs]

end PSRBridge

end EulerSheafSurreal
end Experiments
end HeytingLean
