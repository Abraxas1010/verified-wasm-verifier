import Lean
import HeytingLean.Payments.Types

namespace HeytingLean
namespace Payments
namespace Rules

open Payments

private def parseNat (s : String) : Nat :=
  match s.toNat? with
  | some n => n
  | none => 0

structure Checks where
  allowedRecipient : Bool
  amountOkPerTx    : Bool
  perWindowOk      : Bool -- daily window (backend-managed counters)
  budgetOk         : Bool
  deriving Repr, Inhabited

/- Determine if a recipient is allowed by policy.
   Supports modes: all, custom, verified (via external flag on request).
-/
def recipientAllowed (p : Policy) (recipient : String) (verifiedOk : Bool) : Bool :=
  match p.allowedRecipientsMode with
  | "all" => true
  | "custom" => p.customRecipients.contains recipient
  | "verified" => verifiedOk
  | _ => false

def amountOk (p : Policy) (amount : String) : Bool :=
  parseNat amount ≤ parseNat p.caps_perTx

/- Daily window check: backend maintains `spentToday` counter; we only compare. -/
def perWindowOk (s : State) (p : Policy) (amount : String) : Bool :=
  parseNat s.spentToday + parseNat amount ≤ parseNat p.caps_perDay

private def findBudget (p : Policy) (id : String) : Option Budget :=
  p.budgets.find? (fun b => b.id == id)

private def findBudgetSpend (s : State) (id : String) : BudgetSpend :=
  match s.budgetsSpent.find? (fun kv => kv.fst == id) with
  | some (_, v) => v
  | none => { epoch? := none, spent := "0" }

def budgetOk (p : Policy) (s : State) (req : Request) : Bool :=
  match findBudget p req.budget_id with
  | none => false
  | some b =>
      let spend := findBudgetSpend s req.budget_id
      let spent := parseNat spend.spent
      let amount := parseNat req.amount
      let cap := parseNat b.cap
      spent + amount ≤ cap

def computeChecks (p : Policy) (s : State) (r : Request) : Checks :=
  { allowedRecipient := recipientAllowed p r.recipient (r.verifiedOk.getD false)
  , amountOkPerTx    := amountOk p r.amount
  , perWindowOk      := perWindowOk s p r.amount
  , budgetOk         := budgetOk p s r }

def applyRequest (_p : Policy) (s : State) (r : Request) : State :=
  -- Backend manages resets; we simply increment counters deterministically.
  let spentToday' := toString (parseNat s.spentToday + parseNat r.amount)
  let txCount' := s.txCount + 1
  -- update budget spend entry for r.budget_id
  let updateBudget (lst : List (String × BudgetSpend)) : List (String × BudgetSpend) :=
    let prev := findBudgetSpend s r.budget_id
    let spent0 := parseNat prev.spent
    let updated : BudgetSpend := { epoch? := prev.epoch?, spent := toString (spent0 + parseNat r.amount) }
    let filtered := lst.filter (fun kv => kv.fst ≠ r.budget_id)
    (r.budget_id, updated) :: filtered
  { s with spentToday := spentToday', txCount := txCount', budgetsSpent := updateBudget s.budgetsSpent }

end Rules
end Payments
end HeytingLean
