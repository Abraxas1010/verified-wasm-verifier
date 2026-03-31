import HeytingLean.Genesis.CoGame
import HeytingLean.Genesis.Iterant

/-!
# Genesis.Life

Phase-1 witness object `Life = {Life | Life}` and its phase evaluation.
-/

namespace HeytingLean.Genesis

open CoGame

/-- Phase selection for witness observation. -/
def evalLife (b : Bool) : Iterant Bool :=
  if b then phaseJ else phaseI

@[simp] theorem evalLife_true : evalLife true = phaseJ := by simp [evalLife]
@[simp] theorem evalLife_false : evalLife false = phaseI := by simp [evalLife]

theorem evalLife_neg (b : Bool) : evalLife (!b) = Iterant.shift (evalLife b) := by
  cases b with
  | false =>
      simpa [evalLife] using phaseJ_eq_shift_phaseI
  | true =>
      simpa [evalLife] using phaseI_eq_shift_phaseJ

theorem life_self_left : ∀ n : CoGame.Life.Node, n ∈ CoGame.Life.leftSucc CoGame.Life.root := by
  intro n
  cases n
  simp [CoGame.Life]

theorem life_self_right : ∀ n : CoGame.Life.Node, n ∈ CoGame.Life.rightSucc CoGame.Life.root := by
  intro n
  cases n
  simp [CoGame.Life]

theorem life_is_self_referential : CoGame.Bisim CoGame.Life CoGame.Life :=
  CoGame.life_bisim_self

end HeytingLean.Genesis
