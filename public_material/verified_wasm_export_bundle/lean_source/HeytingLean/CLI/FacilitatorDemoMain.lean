import HeytingLean.Blockchain.Facilitator

/-!
# `facilitator_demo` CLI

Small executable that exercises the Phase 3 facilitator core:
- build a `ValidPayload` via `validate?`,
- apply `settle`,
- show that the same payload cannot validate again (nonce increments).
-/

namespace HeytingLean
namespace CLI
namespace FacilitatorDemo

open HeytingLean.Blockchain.Facilitator

def demoChain : ChainView :=
  { balance := fun a => if a = 1 then 20 else if a = 2 then 3 else 0
    nonce := fun a => if a = 1 then 7 else 0 }

def demoPayload : SignedPayload :=
  { data := { sender := 1, recipient := 2, amount := 12, nonce := 7 }
    signatureOk := true }

def main (args : List String) : IO UInt32 := do
  if args.contains "--help" then
    IO.println "usage: facilitator_demo [--help]"
    return 0

  match validate? demoChain demoPayload with
  | none =>
      IO.eprintln "payload invalid (unexpected in demo)"
      return 1
  | some vp =>
      let chain' := settle demoChain vp
      IO.println s!"before: senderBal={demoChain.balance 1}, recipientBal={demoChain.balance 2}, senderNonce={demoChain.nonce 1}"
      IO.println s!"after:  senderBal={chain'.balance 1}, recipientBal={chain'.balance 2}, senderNonce={chain'.nonce 1}"
      match validate? chain' demoPayload with
      | none =>
          IO.println "replay check: payload no longer validates (nonce increment) ✓"
          return 0
      | some _ =>
          IO.eprintln "replay check failed: payload still validates"
          return 1

end FacilitatorDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.FacilitatorDemo.main args

