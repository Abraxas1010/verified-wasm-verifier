import HeytingLean.LeanSP.Verify.Tactics

/-!
# LeanSP.Verify.VCDischarge

Verification condition generation and discharge.

Given a concrete Yul program and a specification (pre/post), generates VCs
by running the simple evaluator and checking the postcondition holds.
The discharge function attempts to close VCs via evaluation.
-/

namespace LeanSP.Verify

open LeanSP.Yul
open LeanSP.EVM
open LeanSP.Arith

/-- A verification condition: a named proposition to be proved. -/
structure VC where
  name : String
  condition : Prop
  deriving Inhabited

/-- VC generation result. -/
inductive VCResult where
  | discharged : String → VCResult     -- VC name, automatically discharged
  | reverted : String → VCResult      -- VC name, execution reverted (safety check fired)
  | obligation : String → VCResult     -- VC name, requires manual proof
  | evalError : String → VCResult      -- evaluator returned .error
  deriving Repr, Inhabited

/-- Generate and attempt to discharge a VC by running the simple evaluator.
    Given program `stmts`, initial state `st`, and a decidable postcondition check,
    returns whether the VC was discharged or requires manual proof.

    Reverts are reported as `.reverted`, NOT `.discharged` — a program that reverts
    has not satisfied its postcondition. Callers must handle reverts explicitly. -/
def dischargeVC (vcName : String) (stmts : List Stmt) (st : YulState)
    (checkPost : YulState → Bool) : VCResult :=
  match execSimpleBlock stmts st with
  | .ok st' =>
      if checkPost st' then .discharged vcName
      else .obligation vcName
  | .revert _ => .reverted vcName
  | .error => .evalError vcName

/-- Run a batch of VCs. Returns list of results. -/
def dischargeBatch (vcs : List (String × List Stmt × YulState × (YulState → Bool))) :
    List VCResult :=
  vcs.map fun (name, stmts, st, check) => dischargeVC name stmts st check

/-- Check if all VCs in a batch are discharged. -/
def allDischarged (results : List VCResult) : Bool :=
  results.all fun r => match r with | .discharged _ => true | _ => false

/-- End-to-end VC pipeline: generate VCs for a Hoare spec and discharge them.
    This connects the simple evaluator to the VC framework. -/
def verifySimpleSpec (stmts : List Stmt) (mkState : Word256 → Word256 → YulState)
    (checkPost : YulState → Bool)
    (testInputs : List (Word256 × Word256)) : List VCResult := Id.run do
  let mut results : List VCResult := []
  let mut i : Nat := 0
  for (x, y) in testInputs do
    let st := mkState x y
    results := results ++ [dischargeVC s!"vc_{i}" stmts st checkPost]
    i := i + 1
  return results

end LeanSP.Verify
