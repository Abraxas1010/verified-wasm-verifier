import HeytingLean.CDL.ClosureAsCategorical

/-!
# `cdl_mealy_demo`

Runtime smoke tests for the CDL “coalgebra/Mealy” side, plus the bridge to the ClosingTheLoop
closure operator.

This executable is intentionally:
- deterministic,
- lightweight (no subprocesses),
- robust under empty env / empty PATH.
-/

namespace HeytingLean
namespace CDL
namespace MealyDemo

open HeytingLean.CDL.Coalgebra
open HeytingLean.ClosingTheLoop

/-! ## 1) ParaMealy unrolling (endo-alphabet) -/

private def toyParaMealy : ParaMealy Nat Nat Nat where
  P := Nat
  transition := fun
    | (w, i, s) =>
        -- next state, next symbol
        (s + 1, w + i + s)

private def runParaMealyUnroll : IO Unit := do
  let w : Nat := 3
  let i : Nat := 5
  let s : Nat × Nat := (0, 0)

  let m := toyParaMealy
  let mSep := ParaMealy.seq m m
  let mTied := ParaMealy.unroll2_tied m

  let outSep := mSep.transition ((w, w), i, s)
  let outTied := mTied.transition (w, i, s)
  let ok : Bool := decide (outTied = outSep)

  IO.println "[cdl_mealy_demo] ParaMealy: 2-step unroll (endo-alphabet) tying by Δ"
  IO.println s!"  w={w} i={i} s={s}"
  IO.println s!"  sep  params=(w,w) -> {outSep}"
  IO.println s!"  tied param=w      -> {outTied}"
  IO.println s!"  check tied = sep ∘ Δ : {ok}"

/-! ## 2) ClosingTheLoop closure loop (concrete toy MRSystem) -/

namespace ToyMR

open ClosingTheLoop.MR

private def S : MRSystem.{0, 0} where
  A := Nat
  B := Nat
  H := Set.univ
  f := fun a => a
  hf := by trivial
  Sel := Set.univ
  Φf := fun _b => ⟨fun a => a, by trivial⟩
  hΦf := by trivial

private def b : S.B := (0 : Nat)

private def RI : RightInverseAt S b where
  β := fun g =>
    ⟨fun _ => g, by trivial⟩
  right_inv := by
    intro g
    rfl

private def Φ : Selector S :=
  ⟨fun k => ⟨fun a => (show S.B from ((show Nat from a) + (show Nat from k))), by trivial⟩, by trivial⟩

private def sampleA : S.A := (7 : Nat)

end ToyMR

private def runClosureLoop : IO Unit := do
  let bNat : Nat := (show Nat from ToyMR.b)
  let aNat : Nat := (show Nat from ToyMR.sampleA)

  -- ClosingTheLoop Mealy machine (Tier 2)
  let m :
      ClosingTheLoop.Semantics.Mealy.{0, 0, 0} (PUnit.{1}) (ClosingTheLoop.MR.AdmissibleMap ToyMR.S)
        (ClosingTheLoop.MR.Selector ToyMR.S) :=
    ClosingTheLoop.Semantics.MRBridge.closeMachine (S := ToyMR.S) (b := ToyMR.b) ToyMR.RI
  let step1 := m.step ToyMR.Φ PUnit.unit
  let step2 := m.step step1.1 PUnit.unit
  let g1 : Nat := (show Nat from ((step1.2).1 ToyMR.sampleA))
  let g2 : Nat := (show Nat from ((step2.2).1 ToyMR.sampleA))
  let ok1 : Bool := decide (g1 = g2)

  IO.println "[cdl_mealy_demo] ClosingTheLoop: closure loop stabilizes (sample check)"
  IO.println s!"  b={bNat} a={aNat}"
  IO.println s!"  output after 1 step at a: {g1}"
  IO.println s!"  output after 2 steps at a: {g2}"
  IO.println s!"  check (sample) equal: {ok1}"

  -- CDL ParaMealy repackaging (Tier 3 bridge)
  let mp := CDL.Closure.closeMachinePara (S := ToyMR.S) (b := ToyMR.b) ToyMR.RI
  let t1 := mp.transition (PUnit.unit, PUnit.unit, ToyMR.Φ)
  let t2 := mp.transition (PUnit.unit, PUnit.unit, t1.1)
  let h1 : Nat := (show Nat from ((t1.2).1 ToyMR.sampleA))
  let h2 : Nat := (show Nat from ((t2.2).1 ToyMR.sampleA))
  let ok2 : Bool := decide (h1 = h2)

  IO.println "[cdl_mealy_demo] CDL: same closure loop as ParaMealy (sample check)"
  IO.println s!"  output after 1 step at a: {h1}"
  IO.println s!"  output after 2 steps at a: {h2}"
  IO.println s!"  check (sample) equal: {ok2}"

def main (_argv : List String) : IO UInt32 := do
  try
    runParaMealyUnroll
    IO.println ""
    runClosureLoop
    return 0
  catch e =>
    IO.eprintln s!"[cdl_mealy_demo] error: {e}"
    return 1

end MealyDemo
end CDL
end HeytingLean

/-! Expose entry point for the Lake executable target. -/

def main (args : List String) : IO UInt32 :=
  HeytingLean.CDL.MealyDemo.main args
