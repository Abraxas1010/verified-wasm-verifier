import HeytingLean.Constructor.CT.TaskExistence
import HeytingLean.Constructor.CT.InformationSound
import HeytingLean.Constructor.CT.Core

namespace HeytingLean.Tests.Constructor.CTSoundSanity

open HeytingLean.Constructor.CT

#check TaskCT
#check TaskCT.possible
#check TaskCT.possible_seq
#check TaskCT.InfoVariable
#check TaskCT.SuperinformationMedium

-- A tiny inhabitant for compile-time sanity (trivial task semantics).
namespace Examples

variable {σ : Type}  -- intentionally implicit universe

def trivialTaskCT (σ : Type) : TaskCT σ where
  Ctor := Unit
  implements := fun _ _ => True
  seqCtor := fun _ _ => ()
  parCtor := fun _ _ => ()
  implements_seq := by intro _ _ _ _ _ _; trivial
  implements_par := by intro _ _ _ _ _ _; trivial

-- Under the trivial instance, every task is possible.
example (T : HeytingLean.Constructor.CT.Task σ) : (trivialTaskCT σ).possible T := by
  refine ⟨(), ?_⟩
  trivial

def emptyTaskCT (σ : Type) : TaskCT σ where
  Ctor := PEmpty
  implements := fun _ _ => False
  seqCtor := by
    intro c
    nomatch c
  parCtor := by
    intro c
    nomatch c
  implements_seq := by
    intro c₁ c₂ T U h₁ _h₂
    exact False.elim h₁
  implements_par := by
    intro c₁ c₂ T U h₁ _h₂
    exact False.elim h₁

-- Under the empty instance, every task is impossible (non-vacuity check).
example (T : HeytingLean.Constructor.CT.Task σ) : (emptyTaskCT σ).impossible T := by
  intro h
  rcases h with ⟨c, _⟩
  nomatch c

end Examples

end HeytingLean.Tests.Constructor.CTSoundSanity
