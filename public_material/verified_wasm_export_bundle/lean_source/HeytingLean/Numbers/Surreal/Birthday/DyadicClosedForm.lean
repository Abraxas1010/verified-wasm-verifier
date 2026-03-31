import HeytingLean.Numbers.Surreal.Birthday.CanonicalDyadic

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace Birthday

/-- Reduce n/2^k to simplest dyadic form by dividing out powers of 2 from n.
    E.g. 4/2^3 = 1/2 reduces to (1, 1). -/
def dyadicSimplestForm : Int → Nat → Int × Nat
  | n, 0 => (n, 0)
  | n, k + 1 =>
      if n = 0 then (0, 0)
      else if n % 2 = 0 then dyadicSimplestForm (n / 2) k
      else (n, k + 1)

@[simp] theorem dyadicSimplestForm_any_zero (n : Int) :
    dyadicSimplestForm n 0 = (n, 0) := by
  rfl

@[simp] theorem dyadicSimplestForm_zero_succ (k : Nat) :
    dyadicSimplestForm 0 (k + 1) = (0, 0) := by
  simp [dyadicSimplestForm]

/-- Simplest-form reduction preserves birthday: β(n/2^k) = β(n'/2^k')
    where (n', k') = dyadicSimplestForm n k. -/
theorem normalizedBirthday_dyadicPreGame_simplestForm : ∀ (n : Int) (k : Nat),
    normalizedBirthday (LoFProgram.dyadicPreGame n k) =
      normalizedBirthday (LoFProgram.dyadicPreGame (dyadicSimplestForm n k).1
        (dyadicSimplestForm n k).2)
  | _, 0 => by simp
  | n, k + 1 => by
      by_cases h0 : n = 0
      · subst h0
        simp [dyadicSimplestForm, LoFProgram.dyadicPreGame]
        induction k with
        | zero => rfl
        | succ k ih =>
            simp [LoFProgram.dyadicPreGame]
            exact ih
      · by_cases heven : n % 2 = 0
        · simp only [dyadicSimplestForm, if_neg h0, if_pos heven]
          rw [normalizedBirthday_dyadicPreGame_succ_even n k heven]
          exact normalizedBirthday_dyadicPreGame_simplestForm (n / 2) k
        · simp [dyadicSimplestForm, h0, heven]

/-- Birthday of an integer (k=0) is |n|. Corollary of normalizedBirthday_intPreGame. -/
theorem normalizedBirthday_dyadicPreGame_integer (n : Int) :
    normalizedBirthday (LoFProgram.dyadicPreGame n 0) = Int.natAbs n := by
  show normalizedBirthday (LoFProgram.intPreGame n) = Int.natAbs n
  exact normalizedBirthday_intPreGame n

/-- Even numerator at level k+1 reduces to half at level k (birthday-preserving). -/
theorem normalizedBirthday_dyadicPreGame_even_reduce (n : Int) (k : Nat) (h : n % 2 = 0) :
    normalizedBirthday (LoFProgram.dyadicPreGame n (k + 1)) =
      normalizedBirthday (LoFProgram.dyadicPreGame (n / 2) k) :=
  normalizedBirthday_dyadicPreGame_succ_even n k h

end Birthday
end Surreal
end Numbers
end HeytingLean
