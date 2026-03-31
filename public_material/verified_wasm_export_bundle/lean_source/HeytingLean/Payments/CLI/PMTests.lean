import Lean
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.BoolLens
import HeytingLean.Crypto.ZK.R1CSBool
import HeytingLean.Payments.Types
import HeytingLean.Payments.Rules

namespace HeytingLean
namespace Payments
namespace CLI
namespace PMTests

open Crypto
open Crypto.BoolLens
open Payments

def policyFormula4 : Crypto.Form 4 :=
  let v (i : Fin 4) := Crypto.Form.var i
  let a : Crypto.Form 4 := v ⟨0, by decide⟩
  let b : Crypto.Form 4 := v ⟨1, by decide⟩
  let c : Crypto.Form 4 := v ⟨2, by decide⟩
  let d : Crypto.Form 4 := v ⟨3, by decide⟩
  Crypto.Form.and (Crypto.Form.and a b) (Crypto.Form.and c d)

def env4 (f0 f1 f2 f3 : Bool) : BoolLens.Env 4 := fun i =>
  match i.1 with
  | 0 => f0
  | 1 => f1
  | 2 => f2
  | 3 => f3
  | _ => false

def mkPolicy : Policy :=
  { allowedRecipientsMode := "custom"
  , customRecipients := ["0x1111111111111111111111111111111111111111", "0x2222222222222222222222222222222222222222"]
  , caps_perTx := "100"
  , caps_perDay := "500"
  , budgets := [ { id := "ops", cap := "300", unit := "month" }, { id := "ads", cap := "1000", unit := "month" } ] }

def mkState (spentToday : String) (opsSpent : String) : State :=
  { epoch := 0, spentToday := spentToday, txCount := 0, budgetsSpent := [("ops", { epoch? := some 0, spent := opsSpent })] }

def mkReq (amount : String) : Request :=
  { hashedId := "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
  , recipient := "0x1111111111111111111111111111111111111111"
  , amount := amount
  , budget_id := "ops"
  , epoch := 0 }

def assert (cond : Bool) (msg : String) : IO Unit :=
  if cond then pure () else (throw (IO.userError msg))

def testHappy : IO Unit := do
  let p := mkPolicy
  let s := mkState "0" "50"
  let r := mkReq "80"
  let c := Payments.Rules.computeChecks p s r
  assert c.allowedRecipient "allowedRecipient=false"
  assert c.amountOkPerTx "amountOkPerTx=false"
  assert c.perWindowOk "perWindowOk=false"
  assert c.budgetOk "budgetOk=false"
  let φ := policyFormula4
  let ρ : Env 4 := env4 c.allowedRecipient c.amountOkPerTx c.perWindowOk c.budgetOk
  let compiled := Crypto.ZK.R1CSBool.compile φ ρ
  if compiled.assignment compiled.output ≠ (1 : ℚ) then
    throw (IO.userError "happy case output ≠ 1")

def testPerTxFail : IO Unit := do
  let p := mkPolicy
  let s := mkState "0" "50"
  let r := mkReq "1000"
  let c := Payments.Rules.computeChecks p s r
  assert (!c.amountOkPerTx) "amountOkPerTx should be false"
  let φ := policyFormula4
  let ρ : Env 4 := env4 c.allowedRecipient c.amountOkPerTx c.perWindowOk c.budgetOk
  let compiled := Crypto.ZK.R1CSBool.compile φ ρ
  if compiled.assignment compiled.output ≠ (0 : ℚ) then
    throw (IO.userError "per-tx fail output ≠ 0")

def testPerDayFail : IO Unit := do
  let p := mkPolicy
  let s := mkState "450" "50"
  let r := mkReq "100"
  let c := Payments.Rules.computeChecks p s r
  assert (!c.perWindowOk) "perWindowOk should be false"
  let φ := policyFormula4
  let ρ : Env 4 := env4 c.allowedRecipient c.amountOkPerTx c.perWindowOk c.budgetOk
  let compiled := Crypto.ZK.R1CSBool.compile φ ρ
  if compiled.assignment compiled.output ≠ (0 : ℚ) then
    throw (IO.userError "per-day fail output ≠ 0")

def testBudgetFail : IO Unit := do
  let p := mkPolicy
  let s := mkState "0" "290"
  let r := mkReq "20"
  let c := Payments.Rules.computeChecks p s r
  assert (!c.budgetOk) "budgetOk should be false"
  let φ := policyFormula4
  let ρ : Env 4 := env4 c.allowedRecipient c.amountOkPerTx c.perWindowOk c.budgetOk
  let compiled := Crypto.ZK.R1CSBool.compile φ ρ
  if compiled.assignment compiled.output ≠ (0 : ℚ) then
    throw (IO.userError "budget fail output ≠ 0")

def main (_args : List String) : IO UInt32 := do
  try
    testHappy
    testPerTxFail
    testPerDayFail
    testBudgetFail
    IO.println "ok"
    return 0
  catch e =>
    IO.eprintln s!"Payments tests failed: {e}"
    return 1

end PMTests
end CLI
end Payments
end HeytingLean

-- Provide a top-level main alias for the executable linker
open HeytingLean.Payments.CLI.PMTests in
def main (args : List String) : IO UInt32 :=
  HeytingLean.Payments.CLI.PMTests.main args
