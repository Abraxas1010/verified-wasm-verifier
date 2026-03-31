import HeytingLean.Blockchain.PaymentChannels

/-!
# payment_channels_demo CLI

Small executable that exercises the PCN geometry layer on a toy 3-node channel graph.
-/

namespace HeytingLean
namespace CLI
namespace PaymentChannelsDemo

open Blockchain.PaymentChannels
open Sym2

inductive Node
  | A | B | C
  deriving DecidableEq, Repr

open Node

def Node.rank : Node → Nat
  | A => 0
  | B => 1
  | C => 2

instance : LinearOrder Node :=
  LinearOrder.lift' Node.rank (by
    intro a b h
    cases a <;> cases b <;> cases h <;> rfl)

instance : Fintype Node where
  elems := {A, B, C}
  complete := by
    intro x
    cases x <;> simp

def toyGraph : ChannelGraph Node :=
  { edges := ({s(A, B), s(B, C), s(C, A)} : Finset (Sym2 Node))
    cap := fun e =>
      if e = s(A, B) then 10
      else if e = s(B, C) then 5
      else if e = s(C, A) then 8
      else 0
    loopless := by
      intro e he
      simp at he
      rcases he with rfl | rfl | rfl <;> simp }

def toyLiquidity : LiquidityFn Node :=
  fun e v =>
    if e = s(A, B) then
      if v = A then 7 else if v = B then 3 else 0
    else if e = s(B, C) then
      if v = B then 2 else if v = C then 3 else 0
    else if e = s(C, A) then
      if v = C then 3 else if v = A then 5 else 0
    else
      0

def cycleFlow : NetFlow.Flow Node
  | A, B => 1
  | B, C => 1
  | C, A => 1
  | _, _ => 0

def main (args : List String) : IO UInt32 := do
  if args.contains "--help" then
    IO.println "usage: payment_channels_demo [--help]"
    return 0

  let G := toyGraph
  let l := toyLiquidity
  let w := Wealth.pi G l

  IO.println s!"toy wealth: A={w A}, B={w B}, C={w C}"
  IO.println s!"wgBool(toy wealth) = {Algorithmic.wgBool (V := Node) G w}"
  IO.println s!"wgFlowBool(toy wealth) = {AlgorithmicFlow.wgFlowBool (V := Node) G w}"

  let S : Finset Node := {A, B}
  let cin := Cuts.internalCapacity (G := G) S
  let ccut := Cuts.cutCapacity (G := G) S
  let wS := Cuts.wealthIn (G := G) l S
  IO.println s!"S=A,B: internalCap={cin}, cutCap={ccut}, wealth(S)={wS}"

  let f := cycleFlow
  let l' := Rebalancing.apply G l f
  let w' := Wealth.pi G l'
  IO.println s!"after cycle rebalancing: A={w' A}, B={w' B}, C={w' C}"
  IO.println s!"wgBool(after rebalancing) = {Algorithmic.wgBool (V := Node) G w'}"
  IO.println s!"wgFlowBool(after rebalancing) = {AlgorithmicFlow.wgFlowBool (V := Node) G w'}"

  IO.println s!"paymentFeasibleBool A→B a=2 = {Algorithmic.paymentFeasibleBool (V := Node) G w A B 2}"

  let wPay12 := Payments.pay w A B 12
  IO.println s!"after A→B a=12: A={wPay12 A}, B={wPay12 B}, C={wPay12 C}"
  IO.println s!"wgBool(after pay12) = {Algorithmic.wgBool (V := Node) G wPay12}"
  IO.println s!"wgFlowBool(after pay12) = {AlgorithmicFlow.wgFlowBool (V := Node) G wPay12}"
  IO.println s!"cutObstructedBool(after pay12) = {Cuts.Algorithmic.cutObstructedBool (V := Node) G wPay12}"
  IO.println s!"violatingCuts(after pay12).card = {(Cuts.Algorithmic.violatingCuts (V := Node) G wPay12).card}"
  match AlgorithmicFlow.violatingCutFlow? (V := Node) G wPay12 with
  | none =>
      IO.println "violatingCutFlow?(after pay12) = none"
  | some SFlow =>
      IO.println s!"violatingCutFlow?(after pay12).card = {SFlow.card}"
      IO.println s!"cutViolation(violatingCutFlow?) = {decide (Cuts.cutViolation (V := Node) G wPay12 SFlow)}"
  let SB : Finset Node := {B}
  let cinB := Cuts.internalCapacity (G := G) SB
  let ccutB := Cuts.cutCapacity (G := G) SB
  let wB := Cuts.wealthSum (V := Node) wPay12 SB
  IO.println s!"cut witness SB=B: internalCap={cinB}, cutCap={ccutB}, wealthSum={wB}"
  IO.println s!"cutViolation(SB) = {decide (Cuts.cutViolation (V := Node) G wPay12 SB)}"

  IO.println s!"paymentFeasibleBool A→B a=20 = {Algorithmic.paymentFeasibleBool (V := Node) G w A B 20}"

  return 0

end PaymentChannelsDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.PaymentChannelsDemo.main args
