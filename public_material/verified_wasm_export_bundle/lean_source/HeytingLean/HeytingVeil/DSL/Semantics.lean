import HeytingLean.HeytingVeil.DSL.Syntax
import HeytingLean.HeytingVeil.Temporal.Trace

namespace HeytingLean.HeytingVeil.DSL

open HeytingLean.HeytingVeil.Temporal

structure MachineState where
  intVal : String -> Int
  boolVal : String -> Bool
  deriving Inhabited

def boolAsInt (b : Bool) : Int :=
  if b then 1 else 0

def intAsBool (z : Int) : Bool :=
  z != 0

private def lookupHvType (xs : List (String × HvType)) (name : String) : Option HvType :=
  xs.findSome? (fun (entryName, ty) =>
    if entryName == name then some ty else none)

def varType (m : Module) (name : String) : HvType :=
  (lookupHvType m.stateVars name).getD .int

def evalInt (m : Module) (σ : MachineState) : Expr → Int
  | .var name =>
      match varType m name with
      | .int => σ.intVal name
      | .bool => boolAsInt (σ.boolVal name)
  | .intLit n => n
  | .boolLit b => boolAsInt b
  | .add lhs rhs => evalInt m σ lhs + evalInt m σ rhs
  | .le lhs rhs => boolAsInt (evalInt m σ lhs <= evalInt m σ rhs)
  | .eq lhs rhs => boolAsInt (evalInt m σ lhs = evalInt m σ rhs)
  | .not e => boolAsInt (!(intAsBool (evalInt m σ e)))

def evalProp (m : Module) (σ : MachineState) (e : Expr) : Prop :=
  evalInt m σ e != 0

def exprPred (m : Module) (e : Expr) : StatePred MachineState :=
  fun σ => evalProp m σ e

def alwaysExpr (m : Module) (e : Expr) (tr : Trace MachineState) : Prop :=
  ∀ n, evalProp m (tr n) e

def eventuallyExpr (m : Module) (e : Expr) (tr : Trace MachineState) : Prop :=
  ∃ n, evalProp m (tr n) e

private def nthExprOrTruth : List Expr → Nat → Expr
  | [], _ => .boolLit true
  | e :: _, 0 => e
  | _ :: rest, n + 1 => nthExprOrTruth rest n

private def labelledPredicatesAux (m : Module) (exprs : List Expr) :
    Nat → List String → List (String × StatePred MachineState)
  | _, [] => []
  | idx, label :: rest =>
      let e := nthExprOrTruth exprs idx
      (label, exprPred m e) :: labelledPredicatesAux m exprs (idx + 1) rest

def labelledPredicates (m : Module) (labels : List String) (exprs : List Expr) :
    List (String × StatePred MachineState) :=
  labelledPredicatesAux m exprs 0 labels

def safetyPredicates (m : Module) : List (String × StatePred MachineState) :=
  labelledPredicates m m.safetyLabels m.safety

def invariantPredicates (m : Module) : List (String × StatePred MachineState) :=
  labelledPredicates m m.invariantLabels m.invariants

def reachablePredicates (m : Module) : List (String × StatePred MachineState) :=
  labelledPredicates m m.reachableLabels m.reachable

def weakFairPredicates (m : Module) : List (String × StatePred MachineState) :=
  labelledPredicates m m.wfActions m.wfConditions

def strongFairPredicates (m : Module) : List (String × StatePred MachineState) :=
  labelledPredicates m m.sfActions m.sfConditions

theorem evalIntDeterministic (m : Module) (σ : MachineState) (e : Expr) :
    evalInt m σ e = evalInt m σ e := rfl

theorem evalPropDeterministic (m : Module) (σ : MachineState) (e : Expr) :
    evalProp m σ e = evalProp m σ e := rfl

theorem boolVarUsesBoolStore (m : Module) (σ : MachineState) (name : String)
    (hTy : varType m name = .bool) :
    evalInt m σ (.var name) = boolAsInt (σ.boolVal name) := by
  simp [evalInt, hTy]

theorem intVarUsesIntStore (m : Module) (σ : MachineState) (name : String)
    (hTy : varType m name = .int) :
    evalInt m σ (.var name) = σ.intVal name := by
  simp [evalInt, hTy]

end HeytingLean.HeytingVeil.DSL
