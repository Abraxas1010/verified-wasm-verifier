import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.Basic

/-!
# Analytic (Real) geometry for chemistry

This module is intentionally **noncomputable**: it provides Real-valued geometry
for positions in `R^3` and defines distances via `Real.sqrt`.

The computable layer lives in `HeytingLean.Chem.Interactions` and uses `ℚ`.
-/

namespace HeytingLean.Chem.Interactions.Analytic

open BigOperators

noncomputable section

abbrev Scalar : Type := ℝ

abbrev Vec3 : Type := Fin 3 → Scalar

def dist2 (x y : Vec3) : Scalar :=
  (Fintype.elems (α := Fin 3)).sum (fun i => (x i - y i) ^ (2 : Nat))

def dist (x y : Vec3) : Scalar :=
  Real.sqrt (dist2 x y)

@[simp] theorem dist2_self (x : Vec3) : dist2 x x = 0 := by
  simp [dist2]

@[simp] theorem dist_self (x : Vec3) : dist x x = 0 := by
  simp [dist, dist2]

end

end HeytingLean.Chem.Interactions.Analytic
