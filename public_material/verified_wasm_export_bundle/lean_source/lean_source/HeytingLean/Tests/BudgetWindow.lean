import HeytingLean.Payments.Rules
import HeytingLean.Payments.Types

namespace HeytingLean.Tests.BudgetWindow

open HeytingLean.Payments

def expect (msg : String) (b : Bool) : IO Unit := do
  if b then
    pure ()
  else
    throw <| IO.userError s!"BudgetWindow test failed: {msg}"

def run : IO Unit := do
  let p : Policy :=
    { allowedRecipientsMode := "custom"
    , customRecipients := ["0x1111111111111111111111111111111111111111"]
    , caps_perTx := "100"
    , caps_perDay := "500"
    , budgets := [{ id := "ops", cap := "300", unit := "month" }] }
  let sOk : State := { epoch := 0, spentToday := "0", txCount := 0, budgetsSpent := [("ops", { epoch? := some 0, spent := "0" })] }
  let sBad : State := { epoch := 0, spentToday := "0", txCount := 0, budgetsSpent := [("ops", { epoch? := some 0, spent := "290" })] }
  let rOk : Request :=
    { hashedId := "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
    , recipient := "0x1111111111111111111111111111111111111111"
    , amount := "20"
    , budget_id := "ops"
    , epoch := 0
    , walletAddress := "" }
  expect "budgetOk should hold for fresh spend" (Rules.budgetOk p sOk rOk)
  expect "budgetOk should fail near cap" (!Rules.budgetOk p sBad rOk)

def main (_args : List String) : IO UInt32 := do
  try
    run
    IO.println "Budget window passed"
    pure 0
  catch e =>
    IO.eprintln e
    pure 1

end HeytingLean.Tests.BudgetWindow

/-- expose test entry point for lake target. -/
def main (args : List String) : IO UInt32 :=
  HeytingLean.Tests.BudgetWindow.main args

