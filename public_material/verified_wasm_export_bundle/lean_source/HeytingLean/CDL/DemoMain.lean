import HeytingLean.CDL

/-!
# `cdl_demo`

A tiny runtime smoke test for the CDL/Para integration:

- defines a simple parametric “cell” `Nat × Nat → Nat`,
- compares a 2-step unroll with separate parameters `(p₁, p₂)` vs a tied unroll with one `p`,
- shows that tying corresponds to precomposition by the diagonal `Δ p = (p, p)`.

This executable is intentionally lightweight (no file IO) and should run under empty env / empty PATH.
-/

namespace HeytingLean
namespace CDL
namespace Demo

open HeytingLean.CDL.Para
open HeytingLean.CDL.Examples
open HeytingLean.CDL.Examples.FoldingRNN

/-- A toy “cell”: `out = p + a + s`. -/
def natCell : Examples.Cell Nat Nat :=
  ⟨Nat, fun | (p, (a, s)) => p + a + s⟩

def main (_argv : List String) : IO UInt32 := do
  let uSep : ParaHom (Nat × (Nat × Nat)) Nat :=
    FoldingRNN.unroll2_sep (cell := natCell)
  let uTied : ParaHom (Nat × (Nat × Nat)) Nat :=
    FoldingRNN.unroll2_tied (cell := natCell)

  let input : Nat × (Nat × Nat) := (2, (3, 0))

  let outSep := uSep.f (((1 : Nat), (10 : Nat)), input)
  let outTied := uTied.f ((1 : Nat), input)
  let outSepTied := uSep.f (((1 : Nat), (1 : Nat)), input)
  let ok : Bool := decide (outTied = outSepTied)

  IO.println "[cdl_demo] CDL/Para(Type) weight-tying smoke test"
  IO.println s!"  input = {input}"
  IO.println s!"  unroll2_sep params (1,10) = {outSep}"
  IO.println s!"  unroll2_tied param 1      = {outTied}"
  IO.println s!"  unroll2_sep params (1,1)  = {outSepTied}"
  IO.println s!"  check tied = sep ∘ Δ      = {ok}"
  return 0

end Demo
end CDL
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CDL.Demo.main args
