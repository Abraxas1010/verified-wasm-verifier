import HeytingLean.LoF.LeanKernel.Expression

/-!
# LeanKernel.Inductive (Phase 11)

Executable scaffolding for inductive reduction.

This phase introduces a small, *data-driven* interface for **ι-reduction**
specialized to `casesOn`-style recursors:

`casesOn params minors major`

When `major` is a constructor application, we reduce to the corresponding minor
applied to the constructor fields.

This is intentionally minimal and environment-free. Later phases will connect
these rules to a real kernel environment (constants, inductive declarations,
recursors, and δ-reduction).
-/

namespace HeytingLean
namespace LoF
namespace LeanKernel

namespace Inductive

open Expr

variable {Name Param MetaLevel MetaExpr : Type u}

/-! ## Application spine utilities -/

private def getAppFnArgs.go :
    Expr Name Param MetaLevel MetaExpr →
    List (Expr Name Param MetaLevel MetaExpr) →
    Expr Name Param MetaLevel MetaExpr × List (Expr Name Param MetaLevel MetaExpr)
  | .app f a, argsRev => getAppFnArgs.go f (a :: argsRev)
  | e, argsRev => (e, argsRev)

/-- Decompose an expression into its head function and its (left-spine) arguments. -/
def getAppFnArgs (e : Expr Name Param MetaLevel MetaExpr) :
    Expr Name Param MetaLevel MetaExpr × List (Expr Name Param MetaLevel MetaExpr) :=
  getAppFnArgs.go e []

/-- Build an application from a head and a list of arguments. -/
def mkAppN (f : Expr Name Param MetaLevel MetaExpr) (args : List (Expr Name Param MetaLevel MetaExpr)) :
    Expr Name Param MetaLevel MetaExpr :=
  args.foldl (fun acc a => Expr.app acc a) f

/-! ## `casesOn`-style ι-reduction -/

structure CtorSpec (Name : Type u) where
  name : Name
  numParams : Nat := 0
  numFields : Nat
  recursiveFieldPositions : List Nat := []
deriving Repr

/-- A minimal spec for `casesOn`-style recursors.

Lean recursors do not all expose arguments in the same order. We therefore store the
actual explicit argument positions for the first minor and for the major argument.
Minors are still ordered to match `ctors`.
-/
structure CasesOnSpec (Name : Type u) where
  recursor : Name
  firstMinorIdx : Nat
  majorIdx : Nat
  ctors : List (CtorSpec Name)
deriving Repr

structure IotaRules (Name : Type u) where
  beqName : Name → Name → Bool
  casesOnSpecs : List (CasesOnSpec Name)

namespace IotaRules

def empty : IotaRules Name := { beqName := fun _ _ => false, casesOnSpecs := [] }

end IotaRules

private def ctorIndex? (beqName : Name → Name → Bool) (ctors : List (CtorSpec Name)) (c : Name) : Option Nat :=
  let rec go : List (CtorSpec Name) → Nat → Option Nat
    | [], _ => none
    | d :: ds, i =>
        if beqName d.name c then
          some i
        else
          go ds (i + 1)
  go ctors 0

private def ctorArity? (ctors : List (CtorSpec Name)) (idx : Nat) : Option Nat :=
  match ctors[idx]? with
  | some c => some (c.numParams + c.numFields)
  | none => none

private def ctorFieldWindow? (ctors : List (CtorSpec Name)) (idx : Nat) : Option (Nat × Nat) :=
  match ctors[idx]? with
  | some c => some (c.numParams, c.numFields)
  | none => none

private def ctorRecursiveFields? (ctors : List (CtorSpec Name)) (idx : Nat) : Option (List Nat) :=
  match ctors[idx]? with
  | some c => some c.recursiveFieldPositions
  | none => none

def CasesOnSpec.expectedArgs (spec : CasesOnSpec Name) : Nat :=
  let lastMinorIdx :=
    match spec.ctors.length with
    | 0 => spec.firstMinorIdx
    | len + 1 => spec.firstMinorIdx + len
  Nat.max spec.majorIdx lastMinorIdx + 1

private def setArg?
    (xs : List (Expr Name Param MetaLevel MetaExpr))
    (idx : Nat)
    (x : Expr Name Param MetaLevel MetaExpr) :
    Option (List (Expr Name Param MetaLevel MetaExpr)) :=
  match xs, idx with
  | [], _ => none
  | _ :: xs, 0 => some (x :: xs)
  | y :: ys, idx + 1 =>
      match setArg? ys idx x with
      | some ys' => some (y :: ys')
      | none => none

private def natLiteralAsCtorExpr?
    (spec : CasesOnSpec Name)
    (major : Expr Name Param MetaLevel MetaExpr) :
    Option (Expr Name Param MetaLevel MetaExpr) :=
  match major, spec.ctors with
  | .lit (.natVal n), [zeroCtor, succCtor] =>
      if zeroCtor.numParams == 0 && zeroCtor.numFields == 0 &&
          succCtor.numParams == 0 && succCtor.numFields == 1 then
        let rec mkNatExpr : Nat → Expr Name Param MetaLevel MetaExpr
          | 0 => .const zeroCtor.name []
          | k + 1 => .app (.const succCtor.name []) (mkNatExpr k)
        some (mkNatExpr n)
      else
        none
  | _, _ => none

private def casesOnStep?
    (beqName : Name → Name → Bool)
    (spec : CasesOnSpec Name)
    (e : Expr Name Param MetaLevel MetaExpr) :
    Option (Expr Name Param MetaLevel MetaExpr) :=
  let (fn, args) := getAppFnArgs (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) e
  match fn with
  | .const c _ =>
      if beqName c spec.recursor then
        let expected := spec.expectedArgs
        if args.length >= expected then
          let coreArgs := args.take expected
          let tailArgs := args.drop expected
          match coreArgs[spec.majorIdx]? with
          | none => none
          | some major =>
              let major :=
                match natLiteralAsCtorExpr? (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) spec major with
                | some major' => major'
                | none => major
              let (majorFn, majorArgs) :=
                getAppFnArgs (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) major
              match majorFn with
              | .const ctorName _ =>
                  match ctorIndex? (beqName := beqName) (ctors := spec.ctors) ctorName with
                  | none => none
                  | some idx =>
                      match ctorArity? (ctors := spec.ctors) idx with
                      | none => none
                      | some arity =>
                          if majorArgs.length = arity then
                            match ctorFieldWindow? (ctors := spec.ctors) idx,
                                  ctorRecursiveFields? (ctors := spec.ctors) idx,
                                  coreArgs[spec.firstMinorIdx + idx]? with
                            | some (ctorParams, ctorFields), some recursiveFields, some minor =>
                                if majorArgs.length = ctorParams + ctorFields then
                                  let fieldArgs := majorArgs.drop ctorParams
                                  let ihArgs? :=
                                    recursiveFields.mapM fun pos => do
                                      let subterm ← fieldArgs[pos]?
                                      let recursiveArgs ←
                                        setArg? (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr)
                                          coreArgs spec.majorIdx subterm
                                      pure <|
                                        mkAppN
                                          (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr)
                                          fn recursiveArgs
                                  match ihArgs? with
                                  | some ihArgs =>
                                      let reduced :=
                                        mkAppN
                                          (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr)
                                          minor
                                          (fieldArgs ++ ihArgs)
                                      some <|
                                        mkAppN
                                          (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr)
                                          reduced tailArgs
                                  | none => none
                                else
                                  none
                            | _, _, _ => none
                          else
                            none
              | _ => none
        else
          none
      else
        none
  | _ => none

/-- One ι-reduction step using the provided rules, if the expression is a `casesOn` redex. -/
def iotaStep?
    (rules : IotaRules Name)
    (e : Expr Name Param MetaLevel MetaExpr) :
    Option (Expr Name Param MetaLevel MetaExpr) :=
  let rec go : List (CasesOnSpec Name) → Option (Expr Name Param MetaLevel MetaExpr)
    | [] => none
    | s :: ss =>
        match casesOnStep? (Name := Name) (Param := Param) (MetaLevel := MetaLevel) (MetaExpr := MetaExpr) rules.beqName s e with
        | some e' => some e'
        | none => go ss
  go rules.casesOnSpecs

/-! ## Example rules for `Name := String` (used by sanity tests) -/

namespace Examples

def boolCasesOn : CasesOnSpec String :=
  { recursor := "Bool.casesOn"
    firstMinorIdx := 1
    majorIdx := 3
    ctors :=
      [ { name := "Bool.true", numFields := 0 }
      , { name := "Bool.false", numFields := 0 } ] }

def natCasesOn : CasesOnSpec String :=
  { recursor := "Nat.casesOn"
    firstMinorIdx := 1
    majorIdx := 3
    ctors :=
      [ { name := "Nat.zero", numFields := 0 }
      , { name := "Nat.succ", numFields := 1 } ] }

def rules : IotaRules String :=
  { beqName := fun a b => decide (a = b)
    casesOnSpecs := [boolCasesOn, natCasesOn] }

end Examples

end Inductive

end LeanKernel
end LoF
end HeytingLean
