import HeytingLean.MiniC.Semantics

namespace HeytingLean.HeytingVeil.Extract

open HeytingLean

inductive Control
  | running
  | halted
  deriving Repr, DecidableEq, Inhabited

structure MiniCExtractState where
  control : Control
  store : MiniC.Store
  ret? : Option MiniC.Val := none
  deriving Inhabited

def initState (σ : MiniC.Store := MiniC.emptyStore) : MiniCExtractState :=
  { control := .running, store := σ, ret? := none }

end HeytingLean.HeytingVeil.Extract
