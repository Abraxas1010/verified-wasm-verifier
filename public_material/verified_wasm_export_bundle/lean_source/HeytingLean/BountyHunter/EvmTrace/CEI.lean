import HeytingLean.BountyHunter.EvmTrace.Types

namespace HeytingLean.BountyHunter.EvmTrace

def isBoundaryOp (op : String) : Bool :=
  op = "CALL" || op = "DELEGATECALL" || op = "STATICCALL" || op = "CALLCODE"

structure OrderSummary where
  ok : Bool
  firstWrite : Int
  firstBoundary : Int
  deriving Repr, Inhabited, DecidableEq

private def firstIndex (xs : Array Event) (p : Event → Bool) : Int :=
  Id.run do
    let mut i : Nat := 0
    while i < xs.size do
      if p (xs[i]!) then
        return (Int.ofNat i)
      i := i + 1
    return (-1)

def ceiOrderSummary (t : Trace) : OrderSummary :=
  let firstW := firstIndex t.events (fun e => e.op = "SSTORE")
  let firstB := firstIndex t.events (fun e => isBoundaryOp e.op)
  let ok :=
    if firstB = -1 then
      true
    else
      firstW ≠ -1 && firstW < firstB
  { ok := ok, firstWrite := firstW, firstBoundary := firstB }

end HeytingLean.BountyHunter.EvmTrace
