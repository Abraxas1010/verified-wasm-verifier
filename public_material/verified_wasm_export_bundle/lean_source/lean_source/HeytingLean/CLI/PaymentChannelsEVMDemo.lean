import HeytingLean.Blockchain.PaymentChannels
import HeytingLean.Blockchain.PaymentChannels.EVMAdapter.Extractor
import HeytingLean.Blockchain.PaymentChannels.EVMAdapter.SettlementSemantics

/-!
# payment_channels_evm_demo CLI

Small executable that exercises the concrete EVM settlement semantics:
`EVMState → extractChannelGraph → (finite) PCN geometry checks`.
-/

namespace HeytingLean
namespace CLI
namespace PaymentChannelsEVMDemo

open Blockchain.PaymentChannels
open Blockchain.Contracts.Model
open Blockchain.PaymentChannels.EVMAdapter
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

def addrOf : Node → Address
  | A => "1"
  | B => "2"
  | C => "3"

def cfg : ExtractorConfig :=
  { channelContract := "1000"
    registryContract := "2000" }

def toNodeGraph (G : ChannelGraph Address) : ChannelGraph Node :=
  { edges := ({s(A, B), s(B, C), s(C, A)} : Finset (Sym2 Node))
    cap := fun e =>
      if e = s(A, B) then G.cap (s(addrOf A, addrOf B))
      else if e = s(B, C) then G.cap (s(addrOf B, addrOf C))
      else if e = s(C, A) then G.cap (s(addrOf C, addrOf A))
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

def openCycle : Except SettlementSemantics.Error EVMState := do
  let s0 : EVMState :=
    (EVMState.empty)
      |>.withBalance "1" 100
      |>.withBalance "2" 50
      |>.withBalance "3" 75
  let s1 ← SettlementSemantics.settlementStep cfg "1" s0 (.open "1" "2" 10)
  let s2 ← SettlementSemantics.settlementStep cfg "2" s1 (.open "2" "3" 5)
  let s3 ← SettlementSemantics.settlementStep cfg "3" s2 (.open "3" "1" 8)
  pure s3

/-- Hand-constructed state with two open records for the same unordered pair `{1,2}`.

This is not reachable via `SettlementSemantics.settlementStep` (which forbids opening parallel
channels), but it exercises the extractor aggregation policies. -/
def parallelABState : EVMState :=
  let s0 : EVMState :=
    (EVMState.empty)
      |>.withBalance "1" 100
      |>.withBalance "2" 50
  let s1 := setRegistryLength (state := s0) cfg.registryContract 2
  let r0 : ChannelRecord :=
    { participant1 := "1"
      participant2 := "2"
      capacity := 10
      status := .Open }
  let r1 : ChannelRecord :=
    { participant1 := "1"
      participant2 := "2"
      capacity := 7
      status := .Open }
  let s2 := putChannelRecord s1 cfg.channelContract 0 r0
  putChannelRecord s2 cfg.channelContract 1 r1

def main (args : List String) : IO UInt32 := do
  if args.contains "--help" then
    IO.println "usage: payment_channels_evm_demo [--help]"
    return 0
  match openCycle with
  | .error e =>
      IO.eprintln s!"openCycle failed: {repr e}"
      return 1
  | .ok s3 =>
      let GAddr := extractChannelGraph cfg s3
      IO.println s!"Extracted Address-graph edges.card = {GAddr.edges.card}"
      IO.println s!"cap(1,2) = {GAddr.cap (s("1", "2"))}"
      IO.println s!"cap(2,3) = {GAddr.cap (s("2", "3"))}"
      IO.println s!"cap(3,1) = {GAddr.cap (s("3", "1"))}"

      let G := toNodeGraph GAddr
      let l := toyLiquidity
      let w := Wealth.pi G l
      IO.println s!"toy wealth: A={w A}, B={w B}, C={w C}"
      IO.println s!"wgBool(toy wealth) = {Algorithmic.wgBool (V := Node) G w}"
      IO.println s!"wgFlowBool(toy wealth) = {AlgorithmicFlow.wgFlowBool (V := Node) G w}"
      IO.println s!"paymentFeasibleBool A→B a=2 = {Algorithmic.paymentFeasibleBool (V := Node) G w A B 2}"

      match SettlementSemantics.settlementStep cfg "1" s3 (.splice "1" "2" 12) with
      | .error e =>
          IO.eprintln s!"splice(1,2) failed: {repr e}"
          return 1
      | .ok s4 =>
          let GAddr' := extractChannelGraph cfg s4
          IO.println s!"after splice(1,2,newCap=12): cap(1,2) = {GAddr'.cap (s("1", "2"))}"

      let sPar := parallelABState
      let GMax := extractChannelGraph cfg sPar
      let GSum := extractChannelGraphSumCap cfg sPar
      IO.println s!"parallel channels demo: edges.card={GSum.edges.card}"
      IO.println s!"capMax(1,2) = {GMax.cap (s("1", "2"))}"
      IO.println s!"capSum(1,2) = {GSum.cap (s("1", "2"))}"
      return 0

end PaymentChannelsEVMDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.PaymentChannelsEVMDemo.main args
