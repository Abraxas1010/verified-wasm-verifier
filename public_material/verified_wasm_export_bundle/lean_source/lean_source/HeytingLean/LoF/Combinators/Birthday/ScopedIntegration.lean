import HeytingLean.LoF.Combinators.Birthday.DecisionGate

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Birthday

open HeytingLean.LoF
open HeytingLean.LoF.Combinators.SKYUniversality

/-- The scoped birthday metric assigned to the exact self-program fragment. -/
def selfProgramBirthday (program : SelfProgram) : Nat :=
  combBirthday (SKYUniversality.encode program)

@[simp] theorem selfProgramBirthday_base (seed : Comb) :
    selfProgramBirthday (.base seed) = combBirthday seed := by
  change combBirthday seed = combBirthday seed
  rfl

@[simp] theorem selfProgramBirthday_unfold (program : SelfProgram) :
    selfProgramBirthday (.unfold program) = selfProgramBirthday program + 1 := by
  simp [selfProgramBirthday, SKYUniversality.encode, combBirthday, Nat.add_comm]

@[simp] theorem selfProgramBirthday_repeatedUnfold (seed : Comb) :
    ∀ n : Nat, selfProgramBirthday (repeatedUnfold seed n) = combBirthday seed + n
  | 0 => by
      simp [repeatedUnfold, selfProgramBirthday_base]
  | n + 1 => by
      simpa [repeatedUnfold, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        congrArg Nat.succ (selfProgramBirthday_repeatedUnfold seed n)

end Birthday
end Combinators
end LoF
end HeytingLean
