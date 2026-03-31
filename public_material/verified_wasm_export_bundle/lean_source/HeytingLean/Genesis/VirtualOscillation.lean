import HeytingLean.Genesis.Life

/-!
# Genesis.VirtualOscillation

Phase-A virtual-logic oscillator lemmas over the existing Genesis iterant core.
-/

namespace HeytingLean.Genesis

open Iterant

/-- Delayed negation on two-phase Boolean iterants: swap, then negate each phase. -/
def dnot (x : Iterant Bool) : Iterant Bool :=
  ⟨!x.odd, !x.even⟩

@[simp] theorem dnot_even (x : Iterant Bool) : (dnot x).even = !x.odd := rfl
@[simp] theorem dnot_odd (x : Iterant Bool) : (dnot x).odd = !x.even := rfl

/-- Delayed negation is involutive. -/
theorem dnot_dnot (x : Iterant Bool) : dnot (dnot x) = x := by
  cases x with
  | mk even odd =>
      cases even <;> cases odd <;> rfl

@[simp] theorem dnot_phaseI : dnot phaseI = phaseI := by
  rfl

@[simp] theorem dnot_phaseJ : dnot phaseJ = phaseJ := by
  rfl

/-- The only delayed-negation fixed points are the two oscillator phases `I` and `J`. -/
theorem dnot_fixedPoints (x : Iterant Bool) : dnot x = x → x = phaseI ∨ x = phaseJ := by
  intro hx
  cases x with
  | mk even odd =>
      cases even <;> cases odd
      · have : False := by
          simp [dnot] at hx
        exact False.elim this
      · exact Or.inl rfl
      · exact Or.inr rfl
      · have : False := by
          simp [dnot] at hx
        exact False.elim this

/-- Alias for ATP target naming: true-initialized Life evaluates to `J`. -/
theorem evalLife_true_eq_J : evalLife true = phaseJ := evalLife_true

/-- Alias for ATP target naming: false-initialized Life evaluates to `I`. -/
theorem evalLife_false_eq_I : evalLife false = phaseI := evalLife_false

end HeytingLean.Genesis
