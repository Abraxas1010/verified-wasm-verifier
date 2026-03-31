import Mathlib
import HeytingLean.Ontology.DriverChain

/-!
# Euler-Sheaf-Surreal kernel (depth 10)

This module provides a compact, fully computable kernel for experiments that combine:
- Euler-lane phase transport (`eulerShiftDepth10`),
- set/surreal projection (`projectDepth10`, `complementDepth10`), and
- sheaf-style compatibility scoring (`compatPenaltyDepth10`).

The definitions are intentionally finite and arithmetic-friendly so they can be
routed through the certified `LambdaIR -> MiniC -> C` export path.
-/

namespace HeytingLean
namespace Experiments
namespace EulerSheafSurreal

open scoped BigOperators

/-- Fixed surreal truncation depth for the experiment. -/
def maxDepth : Nat := 10

/-- Set/surreal projection to the depth-10 alphabet. -/
def projectDepth10 (n : Nat) : Nat := Nat.min n maxDepth

/-- Depth-10 complement (Euler antiphase partner in this finite lane). -/
def complementDepth10 (n : Nat) : Nat := maxDepth - projectDepth10 n

/-- One-step Euler phase shift on the finite depth-10 ring. -/
def eulerShiftDepth10 (n : Nat) : Nat :=
  let p := projectDepth10 n
  if p = maxDepth then 0 else p + 1

/-- Sheaf overlap compatibility penalty on depth-10 labels. -/
def compatPenaltyDepth10 (a b : Nat) : Nat :=
  let pa := projectDepth10 a
  let pb := projectDepth10 b
  if pa = pb then 0 else if pa + pb = maxDepth then 0 else 1

/-- Unary set-lane bit extracted from projected depth-10 labels. -/
def parityBitDepth10 (n : Nat) : Nat := (projectDepth10 n) % 2

/-- Set-lane unary penalty for parity mismatch. -/
def setBitPenaltyDepth10 (targetBit n : Nat) : Nat :=
  if parityBitDepth10 n = targetBit % 2 then 0 else 1

/-- A compact one-step composite update used by runtime experiments. -/
def eulerSheafSurrealStep (current neighbor : Nat) : Nat :=
  let pc := projectDepth10 current
  let pn := projectDepth10 neighbor
  if compatPenaltyDepth10 pc pn = 0 then pc else eulerShiftDepth10 (complementDepth10 pn)

@[simp] theorem projectDepth10_idempotent (n : Nat) :
    projectDepth10 (projectDepth10 n) = projectDepth10 n := by
  unfold projectDepth10
  exact Nat.min_eq_left (Nat.min_le_right n maxDepth)

theorem projectDepth10_le_maxDepth (n : Nat) : projectDepth10 n ≤ maxDepth := by
  unfold projectDepth10
  exact Nat.min_le_right n maxDepth

theorem projectDepth10_fixed_of_le {n : Nat} (h : n ≤ maxDepth) : projectDepth10 n = n := by
  unfold projectDepth10
  exact Nat.min_eq_left h

theorem complementDepth10_le_maxDepth (n : Nat) : complementDepth10 n ≤ maxDepth := by
  unfold complementDepth10
  omega

@[simp] theorem projectDepth10_complement_fixed (n : Nat) :
    projectDepth10 (complementDepth10 n) = complementDepth10 n := by
  apply projectDepth10_fixed_of_le
  exact complementDepth10_le_maxDepth n

/-- Involutive law modulo projection. -/
@[simp] theorem complementDepth10_involutive_to_projected (n : Nat) :
    complementDepth10 (complementDepth10 n) = projectDepth10 n := by
  unfold complementDepth10
  have hfix : projectDepth10 (maxDepth - projectDepth10 n) = maxDepth - projectDepth10 n := by
    apply projectDepth10_fixed_of_le
    omega
  rw [hfix]
  have hle : projectDepth10 n ≤ maxDepth := projectDepth10_le_maxDepth n
  omega

theorem eulerShiftDepth10_le_maxDepth (n : Nat) : eulerShiftDepth10 n ≤ maxDepth := by
  unfold eulerShiftDepth10
  set p := projectDepth10 n
  by_cases h : p = maxDepth
  · simp [h]
  · have hle : p ≤ maxDepth := by
      simpa [p] using projectDepth10_le_maxDepth n
    simp [h]
    omega

@[simp] theorem projectDepth10_eulerShift_fixed (n : Nat) :
    projectDepth10 (eulerShiftDepth10 n) = eulerShiftDepth10 n := by
  apply projectDepth10_fixed_of_le
  exact eulerShiftDepth10_le_maxDepth n

@[simp] theorem compatPenaltyDepth10_self_zero (a : Nat) : compatPenaltyDepth10 a a = 0 := by
  unfold compatPenaltyDepth10
  simp

@[simp] theorem compatPenaltyDepth10_complement_zero (a : Nat) :
    compatPenaltyDepth10 a (complementDepth10 a) = 0 := by
  unfold compatPenaltyDepth10
  rw [projectDepth10_complement_fixed]
  by_cases hEq : projectDepth10 a = complementDepth10 a
  · simp [hEq]
  · simp [hEq]
    have hle : projectDepth10 a ≤ maxDepth := projectDepth10_le_maxDepth a
    have hsum : projectDepth10 a + complementDepth10 a = maxDepth := by
      unfold complementDepth10
      omega
    simp [hsum]

theorem compatPenaltyDepth10_nonneg (a b : Nat) : 0 ≤ compatPenaltyDepth10 a b := by
  exact Nat.zero_le (compatPenaltyDepth10 a b)

theorem setBitPenaltyDepth10_nonneg (bit n : Nat) : 0 ≤ setBitPenaltyDepth10 bit n := by
  exact Nat.zero_le (setBitPenaltyDepth10 bit n)

theorem eulerSheafSurrealStep_in_range (current neighbor : Nat) :
    projectDepth10 (eulerSheafSurrealStep current neighbor) = eulerSheafSurrealStep current neighbor := by
  unfold eulerSheafSurrealStep
  set pc := projectDepth10 current with hpcDef
  set pn := projectDepth10 neighbor with hpnDef
  by_cases h : compatPenaltyDepth10 pc pn = 0
  · have hpc : projectDepth10 pc = pc := by
      rw [hpcDef]
      exact projectDepth10_idempotent current
    simp [h, hpc]
  · simp [h, projectDepth10_eulerShift_fixed]

/-- Re-exported sheaf witness: re-entry lane has a gluable Euler section. -/
theorem reentry_lane_glues
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) :
    PerspectivalPlenum.LensSheaf.Amalgamates
      Ontology.EulerPhaseWitnessPresheaf
      Ontology.eulerPhaseObj
      (PerspectivalPlenum.LensSheaf.singletonCover Ontology.eulerPhaseObj)
      (Ontology.eulerSingletonFamily ((Ontology.supported_oscillation (R := R)).enhances)
        (Ontology.reentry_supported_enhances_eulerPhaseLaw (R := R))) :=
  Ontology.reentry_supported_singleton_glues (R := R)

/-- Re-exported plenum existence witness for the re-entry Euler process. -/
theorem reentry_lane_existsInPlenum
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) :
    PerspectivalPlenum.LensSheaf.ExistsInPlenum ((Ontology.supported_oscillation (R := R)).enhances) :=
  Ontology.reentry_supported_existsInPlenum (R := R)

/-- Re-exported unified driver witness (sheaf glue + J-ratchet trajectory). -/
theorem reentry_lane_driver_witness
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α)
    {G : Representations.Radial.RadialGraph}
    (js : Representations.Radial.JRatchet.JState G) :
    Ontology.DriverWitness (R := R) (js := js) :=
  Ontology.reentry_driverWitness (R := R) (js := js)

end EulerSheafSurreal
end Experiments
end HeytingLean
