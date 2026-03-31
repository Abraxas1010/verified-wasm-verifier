import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.Combinators.SKYUniversality

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Birthday

open HeytingLean.LoF

/-- Structural birthday-style size surrogate for SKY terms. -/
def combBirthday : Comb → Nat
  | .K => 1
  | .S => 1
  | .Y => 1
  | .app f a => combBirthday f + combBirthday a

/-- Plain node count, kept separate from the birthday surrogate for decision-gate sampling. -/
def combNodeCount : Comb → Nat
  | .K => 1
  | .S => 1
  | .Y => 1
  | .app f a => combNodeCount f + combNodeCount a + 1

/-- Number of enumerated one-step reductions from a term. -/
def stepBranching (t : Comb) : Nat :=
  (Comb.stepEdgesList t).length

@[simp] theorem combBirthday_pos (t : Comb) : 0 < combBirthday t := by
  induction t with
  | K | S | Y => decide
  | app f a ihf iha =>
      simp [combBirthday, ihf, iha]

@[simp] theorem combNodeCount_pos (t : Comb) : 0 < combNodeCount t := by
  induction t with
  | K | S | Y => decide
  | app f a ihf iha =>
      simp [combNodeCount, ihf, iha]

@[simp] theorem combBirthday_I :
    combBirthday Comb.I = 3 := by
  rfl

end Birthday
end Combinators
end LoF
end HeytingLean
