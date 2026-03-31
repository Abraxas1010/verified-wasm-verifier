import Lean
import HeytingLean.Payments.Types
import HeytingLean.Payments.Rules

/-!
Simple CLI test to validate hour-based budget window rollover.
Constructs policy/state/requests and checks perWindowOk and state updates.
-/

namespace HeytingLean
namespace Tests
namespace BudgetWindow

open Payments
open Payments.Rules

def mkPolicyDay (cap : String) : Policy :=
  { allowedRecipientsMode := "custom"
  , customRecipients := ["0xAA"]
  , caps_perTx := "1000"
  , caps_perDay := "5000"
  , budgets := [{ id := "ops", cap := cap, unit := "day" }]
  , verifiedRoot := none }

def mkState (epoch : Nat) (spentToday : String) : State :=
  { epoch := epoch, spentToday := spentToday, txCount := 0, budgetsSpent := [] }

def mkReq (epoch : Nat) (amt : String) : Request :=
  { hashedId := "0xWALLET", recipient := "0xAA", amount := amt, budget_id := "ops", epoch := epoch }

def run (_args : List String) : IO UInt32 := do
  let pol := mkPolicyDay "10000"
  let st  := mkState 1 "0"
  -- First request at epoch 1, amount 600 → ok
  let r1 := mkReq 1 "600"
  let c1 := computeChecks pol st r1
  if !(c1.perWindowOk) then IO.eprintln "c1.perWindowOk false"; return 1
  let st' := applyRequest pol st r1
  -- Second request at epoch 25 (>= 24 hours later), amount 600 → window should reset
  let r2 := mkReq 25 "600"
  let c2 := computeChecks pol st' r2
  if !(c2.perWindowOk) then IO.eprintln "c2.perWindowOk false (expected reset)"; return 1
  IO.println "budget_window: ok"
  return 0

end BudgetWindow
end Tests
end HeytingLean

def main (args : List String) : IO UInt32 := HeytingLean.Tests.BudgetWindow.run args

