import HeytingLean.Logic.BayesResidual
import HeytingLean.Logic.Plausibility
import HeytingLean.Logic.ResiduatedLadder
import HeytingLean.LoF.Instances
import Mathlib.Order.BooleanAlgebra.Basic

/-!
Sanity checks for the plausibility layer (compilation-level).
-/

namespace HeytingLean.Tests

open HeytingLean.Logic
open HeytingLean.Logic.Residuated
open HeytingLean.Logic.DimensionFamily
open HeytingLean.LoF
open Set
open scoped Classical

variable {α : Type u} [PrimaryAlgebra α]
variable (R : Reentry α)

/-- The deduction/abduction faces of the residuation triangle agree. -/
example (a b c : R.Omega) :
    Residuated.deduction (R := R) a b c ↔ Residuated.abduction (R := R) a b c :=
  deduction_iff_abduction (R := R) a b c

/-- A constant dimension family embeds cores by the identity function. -/
def constFamily : DimensionFamily α :=
  { R := fun _ => R
    weakening := by
      intro d x; rfl }

example (d : ℕ) (a : ((constFamily (R := R)).R d).Omega) :
    ((omegaInclusion (F := constFamily (R := R)) d a) : α) = (a : α) :=
  rfl

/-- The trivial strict measure exists for any re-entry nucleus. -/
example : StrictPlausibilityMeasure (R := R) (S := punitScale) :=
  trivialStrictMeasure (R := R)

/-- Numeric residual sanity: with `q = 2`, the residual of `2` at `z = 2` is ≥ 1. -/
example : (1 : ENNReal) ≤ residualMul (2 : ENNReal) 2 := by
  have h := residualMul_residuation (x := (1 : ENNReal)) (q := (2 : ENNReal))
    (z := (2 : ENNReal)) (by simp)
  have hleft : (1 : ENNReal) * (2 : ENNReal) ≤ (2 : ENNReal) := by simp
  exact h.mp hleft

/-- Division lemma sanity: residual with nonzero divisor equals `/`. -/
example : residualMul (2 : ENNReal) (3 : ENNReal) = (3 : ENNReal) / (2 : ENNReal) := by
  simp [residualMul_eq_div]

/-! ### Classical window on `Set Bool`

This is the tiny Cox/Jaynes limit: identity nucleus, support `{true}`,
and a strict plausibility `μBool` concentrated at the boundary element. -/

def setTrue : Set Bool := {b | b = true}
def setFalse : Set Bool := {b | b = false}
def setTop : Set Bool := Set.univ

noncomputable def idNucleusSetBool : Nucleus (Set Bool) where
  toFun := id
  map_inf' := by intro x y; rfl
  idempotent' := by intro x; rfl
  le_apply' := by intro x; rfl

/-- Identity re-entry with support `{true}` as the classical boundary witness. -/
noncomputable def reentryBool : Reentry (Set Bool) := by
  classical
  refine
    { nucleus := idNucleusSetBool
      primordial := setTrue
      counter := setFalse
      support := setTrue
      primordial_mem := rfl
      counter_mem := rfl
      primordial_nonbot := by
        classical
        refine bot_lt_iff_ne_bot.mpr ?_
        intro h
        have hmem : (true : Bool) ∈ (⊥ : Set Bool) := by
          have : (true : Bool) ∈ setTrue := by simp [setTrue]
          simpa [h] using this
        cases hmem
      counter_nonbot := by
        classical
        refine bot_lt_iff_ne_bot.mpr ?_
        intro h
        have hmem : (false : Bool) ∈ (⊥ : Set Bool) := by
          have : (false : Bool) ∈ setFalse := by simp [setFalse]
          simpa [h] using this
        cases hmem
      orthogonal := by
        ext b <;> cases b <;> simp [setTrue, setFalse, inf_eq_inter]
      primordial_in_support := by
        -- `setTrue` is contained in itself.
        exact le_rfl
      map_bot := rfl
      primordial_minimal := by
        intro x hx_fix hx_pos hx_sup
        classical
        have hx_ne : x ≠ (⊥ : Set Bool) := bot_lt_iff_ne_bot.mp hx_pos
        have hx_nonempty : x.Nonempty :=
          Set.nonempty_iff_ne_empty.mpr (by simpa using hx_ne)
        obtain ⟨w, hw⟩ := hx_nonempty
        have hw_true : w = true := by
          have := hx_sup hw
          simpa [setTrue] using this
        have hx_true : true ∈ x := by simpa [hw_true] using hw
        intro b hb
        have hb_true : b = true := by simpa [setTrue] using hb
        subst hb_true
        simpa using hx_true }

noncomputable def μBool (s : Set Bool) : ENNReal :=
  if true ∈ s then 1 else 0

lemma μBool_eq_if_true_mem (s : Set Bool) :
    μBool s = (if true ∈ s then 1 else 0) := by
  classical
  simp [μBool]

lemma μBool_ne_zero_iff (s : Set Bool) :
    μBool s ≠ 0 ↔ true ∈ s := by
  classical
  by_cases h : true ∈ s
  · have : μBool s = 1 := by simp [μBool_eq_if_true_mem, h]
    simp [this, h]
  · have : μBool s = 0 := by simp [μBool_eq_if_true_mem, h]
    simp [this, h]

lemma μBool_empty : μBool (∅ : Set Bool) = 0 := by
  simp [μBool]

lemma μBool_setFalse : μBool setFalse = 0 := by
  simp [μBool, setFalse]

lemma μBool_setTrue : μBool setTrue = 1 := by
  simp [μBool, setTrue]

lemma μBool_univ : μBool (Set.univ : Set Bool) = 1 := by
  simp [μBool]

lemma μBool_imp_eq_residual (B : Set Bool) :
    μBool (setTrue ⇨ B) = μBool B / μBool setTrue := by
  classical
  have hA : μBool setTrue = (1 : ENNReal) := μBool_setTrue
  -- membership of `true` controls `μBool`
  have hmem : (true : Bool) ∈ (setTrue ⇨ B) ↔ (true : Bool) ∈ B := by
    have hsubset :=
      (le_himp_iff (a := ({true} : Set Bool)) (b := setTrue) (c := B))
    have hleft :
        ({true} : Set Bool) ⊆ setTrue ⇨ B ↔ (true : Bool) ∈ setTrue ⇨ B := by
      simp [Set.singleton_subset_iff]
    have hright :
        ({true} : Set Bool) ⊓ setTrue ⊆ B ↔ (true : Bool) ∈ B := by
      simp [Set.singleton_subset_iff, setTrue]
    exact (hleft.symm.trans hsubset).trans hright
  calc
    μBool (setTrue ⇨ B)
        = (if true ∈ (setTrue ⇨ B) then 1 else 0) := μBool_eq_if_true_mem _
    _ = (if true ∈ B then 1 else 0) := by simp [hmem]
    _ = μBool B := by simp [μBool_eq_if_true_mem]
    _ = μBool B / μBool setTrue := by simpa [hA]

example : μBool (setTrue ⇨ setTrue) = 1 := by
  simpa [μBool_setTrue] using μBool_imp_eq_residual (B := setTrue)

example : μBool (setTrue ⇨ setFalse) = 0 := by
  simpa [μBool_setFalse, μBool_setTrue] using μBool_imp_eq_residual (B := setFalse)

/-! ### Cox fragment instantiation on `Set Bool` (test-local) -/

lemma μBool_mono {A B : Set Bool} (hAB : A ⊆ B) :
    μBool A ≤ μBool B := by
  classical
  by_cases hA : true ∈ A
  · have hB : true ∈ B := hAB hA
    simp [μBool, hA, hB]
  · simp [μBool, hA]

lemma μBool_add_disjoint {A B : Set Bool} (hdis : Disjoint A B) :
    μBool (A ∪ B) = μBool A + μBool B := by
  classical
  have hdis' := disjoint_left.mp hdis
  by_cases hA : true ∈ A
  · have hB : true ∉ B := by
      intro hb
      exact (hdis' hA hb).elim
    simp [μBool, hA, hB]
  · by_cases hB : true ∈ B
    · have hA' : true ∉ A := hA
      simp [μBool, hA', hB]
    · simp [μBool, hA, hB]

lemma μBool_compl (A : Set Bool) : μBool A + μBool Aᶜ = 1 := by
  classical
  by_cases hA : true ∈ A
  · have hAc : true ∉ Aᶜ := by
      simpa using hA
    simp [μBool, hA, hAc]
  · have hAc : true ∈ Aᶜ := by
      simpa using hA
    simp [μBool, hA, hAc]

noncomputable def condBool (A B : Set Bool) : ENNReal :=
  if _hA : μBool A = 0 then 0 else μBool (A ∩ B) / μBool A

lemma condBool_spec {A B : Set Bool} (hA : μBool A ≠ 0) :
    condBool A B = μBool (A ∩ B) / μBool A := by
  simp [condBool, hA]

example : condBool setTrue setTrue = 1 := by
  simp [condBool, μBool, setTrue]

example : condBool setTrue setFalse = 0 := by
  simp [condBool, μBool, setTrue, setFalse]

/-! ### A slightly richer finite window: identity nucleus on `Set (Fin 2)` -/

def setZero : Set (Fin 2) := {i | i = 0}
def setOne  : Set (Fin 2) := {i | i = 1}

noncomputable def reentryFin2 : Reentry (Set (Fin 2)) := by
  classical
  refine
    { nucleus := ⊥
      primordial := setZero
      counter := setOne
      support := setZero
      primordial_mem := rfl
      counter_mem := rfl
      primordial_nonbot := by
        refine bot_lt_iff_ne_bot.mpr ?_
        intro h
        have : (0 : Fin 2) ∈ (⊥ : Set (Fin 2)) := by
          have : (0 : Fin 2) ∈ setZero := by simp [setZero]
          simpa [h] using this
        cases this
      counter_nonbot := by
        refine bot_lt_iff_ne_bot.mpr ?_
        intro h
        have : (1 : Fin 2) ∈ (⊥ : Set (Fin 2)) := by
          have : (1 : Fin 2) ∈ setOne := by simp [setOne]
          simpa [h] using this
        cases this
      orthogonal := by
        ext i
        constructor
        · intro hi
          rcases hi with ⟨h0, h1⟩
          cases h0
          cases h1
        · intro hi; cases hi
      primordial_in_support := by
        -- `setZero` is contained in itself.
        exact le_rfl
      map_bot := by
        -- The bottom nucleus is the identity.
        simp
      primordial_minimal := by
        intro x hx_fix hx_pos hx_sup
        classical
        have hx_ne : x ≠ (⊥ : Set (Fin 2)) := bot_lt_iff_ne_bot.mp hx_pos
        have hx_nonempty : x.Nonempty :=
          Set.nonempty_iff_ne_empty.mpr (by simpa using hx_ne)
        obtain ⟨w, hw⟩ := hx_nonempty
        have hw0 : w = 0 := by
          have := hx_sup hw
          simpa [setZero] using this
        have hx0 : (0 : Fin 2) ∈ x := by simpa [hw0] using hw
        intro i hi
        have hi0 : i = 0 := by simpa [setZero] using hi
        subst hi0
        simpa using hx0 }

noncomputable def μFin2 (s : Set (Fin 2)) : ENNReal :=
  if (0 : Fin 2) ∈ s then 1 else 0

lemma μFin2_empty : μFin2 (∅ : Set (Fin 2)) = 0 := by
  simp [μFin2]

lemma μFin2_setZero : μFin2 setZero = 1 := by
  simp [μFin2, setZero]

lemma μFin2_setOne : μFin2 setOne = 0 := by
  simp [μFin2, setOne]

lemma μFin2_univ : μFin2 (Set.univ : Set (Fin 2)) = 1 := by
  simp [μFin2]

lemma μFin2_mono {A B : Set (Fin 2)} (hAB : A ⊆ B) : μFin2 A ≤ μFin2 B := by
  classical
  by_cases h0 : (0 : Fin 2) ∈ A
  · have h0B : (0 : Fin 2) ∈ B := hAB h0
    simp [μFin2, h0, h0B]
  · by_cases h0B : (0 : Fin 2) ∈ B
    · simp [μFin2, h0, h0B]
    · simp [μFin2, h0, h0B]

noncomputable def condFin2 (A B : Set (Fin 2)) : ENNReal :=
  if _hA : μFin2 A = 0 then 0 else μFin2 (A ∩ B) / μFin2 A

lemma condFin2_spec {A B : Set (Fin 2)} (hA : μFin2 A ≠ 0) :
    condFin2 A B = μFin2 (A ∩ B) / μFin2 A := by
  simp [condFin2, hA]

-- Bayes-as-residual for the only nonzero antecedent in this window.
lemma μFin2_imp_setZero (B : Set (Fin 2)) :
    μFin2 (setZero ⇨ B) = μFin2 B / μFin2 setZero := by
  classical
  have hmem : (0 : Fin 2) ∈ (setZero ⇨ B) ↔ (0 : Fin 2) ∈ B := by
    by_cases hB : (0 : Fin 2) ∈ B
    · simp [himp_eq, setZero, hB]
    · simp [himp_eq, setZero, hB]
  calc
    μFin2 (setZero ⇨ B)
        = (if (0 : Fin 2) ∈ (setZero ⇨ B) then 1 else 0) := by
            simp [μFin2]
    _ = (if (0 : Fin 2) ∈ B then 1 else 0) := by simp [hmem]
    _ = μFin2 B := by simp [μFin2]
    _ = μFin2 B / μFin2 setZero := by simp [μFin2_setZero]

example : condFin2 setZero setZero = 1 := by
  simp [condFin2, μFin2, setZero]

example : condFin2 setZero setOne = 0 := by
  simp [condFin2, μFin2, setZero, setOne]

example : μFin2 (setZero ⇨ setZero) = μFin2 setZero / μFin2 setZero := by
  simpa using μFin2_imp_setZero (B := setZero)

example : μFin2 (setZero ⇨ setOne) = μFin2 setOne / μFin2 setZero := by
  simpa using μFin2_imp_setZero (B := setOne)

/-- A classical window on `Set (Fin 2)` (coincides with `Ω` when the nucleus is the identity). -/
noncomputable def fin2Window : ClassicalWindow (Set (Fin 2)) := by
  classical
  refine
    { carrier := Set.univ
      nonempty := by simp
      closed_top := by simp
      closed_bot := by simp
      closed_inf := by
        intro a b ha hb
        simp
      closed_sup := by
        intro a b ha hb
        simp
      closed_himp := by
        intro a b ha hb
        simp [himp_eq]
      double_neg_eq := by
        intro a ha
        ext i
        simp [himp_eq] }

/-- Strict plausibility measure on the finite `Fin 2` re-entry core. -/
noncomputable def μFin2Strict :
    StrictPlausibilityMeasure (R := reentryFin2) (S := ennrealScale) :=
  { μ := fun _ => 1
    monotone := by
      intro a b h
      simpa
    μ_top := rfl
    μ_inf := by
      intro a b
      change (1 : ENNReal) = 1 * 1
      simp
    μ_imp_le := by
      intro a b
      change (1 : ENNReal) ≤ residualMul 1 1
      simp [residualMul]
    μ_imp_eq := by
      intro a b
      change (1 : ENNReal) = residualMul 1 1
      simp [residualMul] }

lemma μFin2Strict_div (a b : reentryFin2.Omega) :
    μFin2Strict.toPlausibilityMeasure.μ (a ⇨ b) =
      μFin2Strict.toPlausibilityMeasure.μ b /
        μFin2Strict.toPlausibilityMeasure.μ a := by
  have hpos : μFin2Strict.toPlausibilityMeasure.μ a ≠ 0 := by simp [μFin2Strict]
  simpa using
    (StrictPlausibilityMeasure.himp_div
      (R := reentryFin2) (μ := μFin2Strict) (a := a) (b := b) hpos)

example :
    μFin2Strict.toPlausibilityMeasure.μ
        ((Reentry.process (R := reentryFin2)) ⇨
          (Reentry.process (R := reentryFin2))) = 1 := by
  simpa [μFin2Strict] using
    μFin2Strict_div (a := Reentry.process (R := reentryFin2))
      (b := Reentry.process (R := reentryFin2))

example :
    μFin2Strict.toPlausibilityMeasure.μ
        ((Reentry.process (R := reentryFin2)) ⇨
          (Reentry.counterProcess (R := reentryFin2))) = 1 := by
  simpa [μFin2Strict] using
    μFin2Strict_div (a := Reentry.process (R := reentryFin2))
      (b := Reentry.counterProcess (R := reentryFin2))

end HeytingLean.Tests
