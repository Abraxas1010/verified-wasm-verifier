import Mathlib.Data.Real.Basic

/-!
# Tropical.Semiring

Minimal “max-plus with -∞” tropical carrier used for lightweight demos.

This is intentionally small and self-contained: it provides the operations and a few algebraic
lemmas needed by `HeytingLean.Tropical.ReLU`, without committing to a full tropical geometry API.
-/

namespace HeytingLean.Tropical

/-- A tiny tropical carrier: `ℝ ∪ {-∞}`. -/
inductive TropicalReal where
  | negInf : TropicalReal
  | finite : ℝ → TropicalReal

namespace TropicalReal

/-- Tropical addition: `max` (with `-∞` as identity). -/
def tadd : TropicalReal → TropicalReal → TropicalReal
  | negInf, b => b
  | a, negInf => a
  | finite a, finite b => finite (max a b)

/-- Tropical multiplication: `+` (with `-∞` as absorbing). -/
def tmul : TropicalReal → TropicalReal → TropicalReal
  | negInf, _ => negInf
  | _, negInf => negInf
  | finite a, finite b => finite (a + b)

instance : Add TropicalReal := ⟨tadd⟩
instance : Mul TropicalReal := ⟨tmul⟩
instance : Zero TropicalReal := ⟨negInf⟩
instance : One TropicalReal := ⟨finite 0⟩

@[simp] theorem negInf_add (b : TropicalReal) : negInf + b = b := by
  cases b <;> rfl

@[simp] theorem add_negInf (a : TropicalReal) : a + negInf = a := by
  cases a <;> rfl

@[simp] theorem finite_add_finite (a b : ℝ) :
    finite a + finite b = finite (max a b) := by
  rfl

@[simp] theorem negInf_mul (b : TropicalReal) : negInf * b = negInf := by
  cases b <;> rfl

@[simp] theorem mul_negInf (a : TropicalReal) : a * negInf = negInf := by
  cases a <;> rfl

@[simp] theorem finite_mul_finite (a b : ℝ) :
    finite a * finite b = finite (a + b) := by
  rfl

/-- A forgetful projection to `ℝ` (used only for demo lemmas).

`negInf` is mapped to `0` purely for convenience; the “right” codomain for a faithful embedding
would be an extended real type. -/
def toReal : TropicalReal → ℝ
  | negInf => 0
  | finite r => r

theorem tadd_comm (a b : TropicalReal) : a + b = b + a := by
  cases a with
  | negInf =>
      cases b <;> rfl
  | finite a =>
      cases b with
      | negInf => rfl
      | finite b =>
          change TropicalReal.finite (max a b) = TropicalReal.finite (max b a)
          exact congrArg TropicalReal.finite (max_comm a b)

theorem tadd_assoc (a b c : TropicalReal) : a + b + c = a + (b + c) := by
  cases a <;> cases b <;> cases c <;> try rfl
  · rename_i a b c
    change
      TropicalReal.finite (max (max a b) c) = TropicalReal.finite (max a (max b c))
    exact congrArg TropicalReal.finite (max_assoc a b c)

theorem tmul_comm (a b : TropicalReal) : a * b = b * a := by
  cases a <;> cases b <;> try rfl
  · rename_i a b
    change TropicalReal.finite (a + b) = TropicalReal.finite (b + a)
    exact congrArg TropicalReal.finite (add_comm a b)

theorem tmul_assoc (a b c : TropicalReal) : a * b * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;> try rfl
  · rename_i a b c
    change TropicalReal.finite (a + b + c) = TropicalReal.finite (a + (b + c))
    exact congrArg TropicalReal.finite (add_assoc a b c)

theorem tmul_distrib (a b c : TropicalReal) : a * (b + c) = a * b + a * c := by
  cases a <;> cases b <;> cases c <;> try rfl
  · rename_i a b c
    change
      TropicalReal.finite (a + max b c) =
        TropicalReal.finite (max (a + b) (a + c))
    exact congrArg TropicalReal.finite (add_max a b c)

end TropicalReal

end HeytingLean.Tropical
