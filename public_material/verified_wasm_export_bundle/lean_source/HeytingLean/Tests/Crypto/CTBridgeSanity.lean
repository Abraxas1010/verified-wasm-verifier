import Mathlib.Tactic
import HeytingLean.Constructor.Crypto

/-!
# CT → UC bridge sanity tests

Compile-time checks for the Phase 7 bridge layer.
-/

namespace HeytingLean.Tests.Crypto.CTBridgeSanity

open HeytingLean.Constructor
open HeytingLean.Security.Composable

namespace Demo

open HeytingLean.Constructor.CT
open HeytingLean.Constructor.Crypto

universe u

/-- A tiny ideal functionality for testing. -/
def F : IdealFunctionality where
  Input := Unit
  Output := Unit
  Leakage := Unit
  compute := fun _ => ((), ())

/-- A tiny protocol for testing. -/
def π : Protocol F where
  State := Unit
  Message := Unit
  init := ()
  execute := fun _ _ => ((), (), ())

/-- A toy `TaskCT` where only the empty task is implementable. -/
def CT : TaskCT Bool where
  Ctor := Unit
  implements := fun _ T => T = { arcs := [] }
  seqCtor := fun _ _ => ()
  parCtor := fun _ _ => ()
  implements_seq := by
    intro c₁ c₂ T U hT hU
    subst hT; subst hU
    simp [Task.seq]
  implements_par := by
    intro c₁ c₂ T U hT hU
    subst hT; subst hU
    simp [Task.par]

def bad : BadTask Bool :=
  ⟨HeytingLean.Constructor.CT.Examples.swapTaskBool⟩

example : CT.impossible bad.task := by
  intro h
  rcases h with ⟨c, hc⟩
  -- `swapTaskBool` is not the empty task (`arcs` has length 2).
  have : (HeytingLean.Constructor.CT.Examples.swapTaskBool.arcs.length = 2) := by rfl
  -- If `swapTaskBool = {arcs := []}` we get `2 = 0`.
  have hlen : (HeytingLean.Constructor.CT.Examples.swapTaskBool.arcs.length = 0) := by
    simpa [TaskCT, CT] using congrArg (fun T => T.arcs.length) hc
  nlinarith

def R : CTtoUCReduction (CT := CT) (Tbad := bad) F where
  π := π
  sim :=
    { SimState := Unit
      init := ()
      simulate := fun _ _ => ((), ()) }
  Indistinguishable := fun _ _ => True
  reduction := by
    intro h
    exact False.elim (h trivial)

example : UCSecure F R.π :=
  ct_to_uc_security (R := R) (hBad := by
    intro h
    rcases h with ⟨c, hc⟩
    have : (HeytingLean.Constructor.CT.Examples.swapTaskBool.arcs.length = 2) := by rfl
    have hlen : (HeytingLean.Constructor.CT.Examples.swapTaskBool.arcs.length = 0) := by
      simpa [TaskCT, CT] using congrArg (fun T => T.arcs.length) hc
    nlinarith)

end Demo

end HeytingLean.Tests.Crypto.CTBridgeSanity
