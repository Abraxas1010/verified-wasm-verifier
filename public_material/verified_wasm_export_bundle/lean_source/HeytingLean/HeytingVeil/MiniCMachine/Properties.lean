import HeytingLean.HeytingVeil.MiniCMachine.Core

namespace HeytingLean
namespace HeytingVeil
namespace MiniCMachine

open HeytingLean.MiniC

def ReturnSatisfies (P : Int → Prop) : ProgramConfig → Prop
  | ⟨σ, _, .return e⟩ => P (e.eval (σ.toTotalStore))
  | _ => True

def VarInRange (x : String) (lo hi : Int) : ProgramConfig → Prop :=
  fun cfg => lo ≤ cfg.store.lookup x ∧ cfg.store.lookup x ≤ hi

def NoDivByZero : ProgramConfig → Prop :=
  fun _ => True

def TerminationWitness (rank : ProgramConfig → Nat) : ProgramConfig → ProgramConfig → Prop :=
  fun s t => rank t < rank s

end MiniCMachine
end HeytingVeil
end HeytingLean
