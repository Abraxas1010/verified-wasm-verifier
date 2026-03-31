import HeytingLean.MirandaDynamics.Discrete.HaltingToPeriodic

/-!
# `miranda_discrete_demo`

A tiny runtime demo for the fully-discrete “halting ↔ reaching a periodic orbit” construction.

This demo is intentionally lightweight:
- no file IO,
- should not crash under empty env / empty PATH,
- prints a short prefix of the trajectory for a halting code and a diverging code.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Discrete

open Nat.Partrec
open Nat.Partrec.Code

def showState : State → String
  | Sum.inl k => s!"search(k={k})"
  | Sum.inr b => s!"cycle(b={b})"

def printPrefix (n : Nat) (c : Code) (label : String) (steps : Nat) : IO Unit := do
  IO.println s!"[{label}] input n={n}"
  for i in List.range (steps + 1) do
    let s := (step n c)^[i] start
    IO.println s!"  t={i}: {showState s}"

def main (_argv : List String) : IO UInt32 := do
  -- Pick a small input.
  let n := 0
  -- A clearly halting code (constant 0).
  let cHalt : Code := Code.const 0
  -- A clearly diverging code: `rfind' succ` searches for an `m` with `succ m = 0`, impossible.
  let cDiv : Code := Code.rfind' Code.succ

  IO.println "[miranda_discrete_demo] discrete halting ↔ reach periodic orbit (period 2)"
  IO.println ""
  printPrefix n cHalt "halts" 8
  IO.println ""
  printPrefix n cDiv "diverges" 8
  return 0

end Discrete
end MirandaDynamics
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.MirandaDynamics.Discrete.main args

