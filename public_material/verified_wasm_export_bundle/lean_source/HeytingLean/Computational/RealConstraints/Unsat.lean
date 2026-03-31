import Lean.Data.Json
import Std.Data.HashMap
import HeytingLean.Computational.RealConstraints.IR
import HeytingLean.Computational.RealConstraints.Cert

namespace HeytingLean
namespace Computational
namespace RealConstraints

open Lean
open Lean.Json

namespace Unsat

structure VarBounds where
  lo : Float
  hi : Float
  loStrict : Bool := false
  hiStrict : Bool := false
deriving Repr, Inhabited

abbrev BoundsMap := Std.HashMap String VarBounds

def boundsMapOfProblem (p : Problem) : BoundsMap :=
  p.vars.foldl (init := ({} : BoundsMap)) (fun acc v => acc.insert v.name { lo := v.lo, hi := v.hi })

def updateVar (m : BoundsMap) (name : String) (f : VarBounds → VarBounds) : BoundsMap :=
  match m.get? name with
  | some b => m.insert name (f b)
  | none => m

def varNonneg (m : BoundsMap) (name : String) : Bool :=
  match m.get? name with
  | some b => b.lo ≥ 0.0
  | none => false

def varNonpos (m : BoundsMap) (name : String) : Bool :=
  match m.get? name with
  | some b => b.hi ≤ 0.0
  | none => false

private def tightenHi (b : VarBounds) (c : Float) (strict : Bool) : VarBounds :=
  if c < b.hi then
    { b with hi := c, hiStrict := strict }
  else if c == b.hi then
    { b with hiStrict := b.hiStrict || strict }
  else
    b

private def tightenLo (b : VarBounds) (c : Float) (strict : Bool) : VarBounds :=
  if c > b.lo then
    { b with lo := c, loStrict := strict }
  else if c == b.lo then
    { b with loStrict := b.loStrict || strict }
  else
    b

mutual

partial def exprNonneg (m : BoundsMap) : Expr → Bool
  | .var name => varNonneg m name
  | .const v => v ≥ 0.0
  | .add xs => xs.all (exprNonneg m)
  | .neg e => exprNonpos m e
  | .pow base exp =>
      if exp == 0 then
        true
      else if exp % 2 == 0 then
        true
      else
        exprNonneg m base
  | .mul xs =>
      if xs.any (fun e => match e with | .const v => v == 0.0 | _ => false) then
        true
      else if xs.all (exprNonneg m) then
        true
      else if xs.all (exprNonpos m) then
        xs.size % 2 == 0
      else
        false

partial def exprNonpos (m : BoundsMap) : Expr → Bool
  | .var name => varNonpos m name
  | .const v => v ≤ 0.0
  | .add xs => xs.all (exprNonpos m)
  | .neg e => exprNonneg m e
  | .pow base exp =>
      if exp == 0 then
        false
      else if exp % 2 == 0 then
        false
      else
        exprNonpos m base
  | .mul xs =>
      if xs.any (fun e => match e with | .const v => v == 0.0 | _ => false) then
        true
      else if xs.all (exprNonneg m) then
        false
      else if xs.all (exprNonpos m) then
        xs.size % 2 == 1
      else
        false

end

def swapCmp : CmpOp → CmpOp
  | .lt => .gt
  | .le => .ge
  | .eq => .eq
  | .ge => .le
  | .gt => .lt

def collectConjCmps : Formula → Option (Array (CmpOp × Expr × Expr))
  | .cmp op lhs rhs => some #[(op, lhs, rhs)]
  | .and xs =>
      xs.foldl
        (init := some (#[] : Array (CmpOp × Expr × Expr)))
        (fun acc f =>
          match acc, collectConjCmps f with
          | some a, some b => some (a ++ b)
          | _, _ => none)
  | _ => none

def tightenBoundsFromCmp (m : BoundsMap) (cmp : CmpOp × Expr × Expr) : BoundsMap :=
  let (op, lhs, rhs) := cmp
  let lhsVar? : Option String := match lhs with | .var n => some n | _ => none
  let rhsVar? : Option String := match rhs with | .var n => some n | _ => none
  let lhsConst? : Option Float := match lhs with | .const v => some v | _ => none
  let rhsConst? : Option Float := match rhs with | .const v => some v | _ => none
  match lhsVar?, rhsConst? with
  | some x, some c =>
      match op with
      | .le => updateVar m x (fun b => tightenHi b c false)
      | .lt => updateVar m x (fun b => tightenHi b c true)
      | .ge => updateVar m x (fun b => tightenLo b c false)
      | .gt => updateVar m x (fun b => tightenLo b c true)
      | .eq =>
          updateVar m x (fun b =>
            if c < b.lo || c > b.hi || (c == b.lo && b.loStrict) || (c == b.hi && b.hiStrict) then
              { b with lo := c, hi := c, loStrict := true, hiStrict := true }
            else
              { b with lo := c, hi := c, loStrict := false, hiStrict := false })
  | _, _ =>
      match lhsConst?, rhsVar? with
      | some c, some x =>
          match op with
          | .le => updateVar m x (fun b => tightenLo b c false)
          | .lt => updateVar m x (fun b => tightenLo b c true)
          | .ge => updateVar m x (fun b => tightenHi b c false)
          | .gt => updateVar m x (fun b => tightenHi b c true)
          | .eq =>
              updateVar m x (fun b =>
                if c < b.lo || c > b.hi || (c == b.lo && b.loStrict) || (c == b.hi && b.hiStrict) then
                  { b with lo := c, hi := c, loStrict := true, hiStrict := true }
                else
                  { b with lo := c, hi := c, loStrict := false, hiStrict := false })
      | _, _ => m

def deriveBounds (p : Problem) (cmps : Array (CmpOp × Expr × Expr)) : BoundsMap :=
  cmps.foldl (init := boundsMapOfProblem p) (fun acc c => tightenBoundsFromCmp acc c)

inductive UnsatReason where
  | boundsContradiction (var : String) (lo : Float) (hi : Float)
  | nonnegLeNeg (cmpIndex : Nat)
  | nonposGePos (cmpIndex : Nat)
deriving Repr, Inhabited

def UnsatReason.toJson : UnsatReason → Json
  | .boundsContradiction v lo hi =>
      Json.mkObj
        [ ("kind", Json.str "bounds_contradiction")
        , ("var", Json.str v)
        , ("lo", Cert.jsonOfFloat lo)
        , ("hi", Cert.jsonOfFloat hi)
        ]
  | .nonnegLeNeg i =>
      Json.mkObj
        [ ("kind", Json.str "nonneg_le_neg")
        , ("cmp_index", Json.num (JsonNumber.fromNat i))
        ]
  | .nonposGePos i =>
      Json.mkObj
        [ ("kind", Json.str "nonpos_ge_pos")
        , ("cmp_index", Json.num (JsonNumber.fromNat i))
        ]

private def floatOfJson (j : Json) : Except String Float := do
  match j with
  | .num n => pure n.toFloat
  | .str s =>
      match Json.parse s.trim with
      | .ok (.num n) => pure n.toFloat
      | _ => throw "expected numeric string"
  | _ => throw "expected number"

def UnsatReason.ofJson (j : Json) : Except String UnsatReason := do
  let obj ← j.getObj?
  let kind ←
    match obj.get? "kind" with
    | some (.str s) => pure s
    | _ => throw "unsat_cert.kind missing/invalid"
  match kind with
  | "bounds_contradiction" =>
      let var ←
        match obj.get? "var" with
        | some (.str s) => pure s
        | _ => throw "unsat_cert.var missing/invalid"
      let loJ := obj.get? "lo" |>.getD (Json.num (JsonNumber.fromNat 0))
      let hiJ := obj.get? "hi" |>.getD (Json.num (JsonNumber.fromNat 0))
      let lo ←
        match floatOfJson loJ with
        | .ok x => pure x
        | .error _ => throw "unsat_cert.lo invalid"
      let hi ←
        match floatOfJson hiJ with
        | .ok x => pure x
        | .error _ => throw "unsat_cert.hi invalid"
      pure (.boundsContradiction var lo hi)
  | "nonneg_le_neg" =>
      let iJson := obj.get? "cmp_index" |>.getD Json.null
      let iInt ←
        match iJson.getInt? with
        | .ok k => pure k
        | .error _ => throw "unsat_cert.cmp_index missing/invalid"
      if iInt < 0 then
        throw "unsat_cert.cmp_index must be nonnegative"
      let i : Nat := iInt.toNat
      pure (.nonnegLeNeg i)
  | "nonpos_ge_pos" =>
      let iJson := obj.get? "cmp_index" |>.getD Json.null
      let iInt ←
        match iJson.getInt? with
        | .ok k => pure k
        | .error _ => throw "unsat_cert.cmp_index missing/invalid"
      if iInt < 0 then
        throw "unsat_cert.cmp_index must be nonnegative"
      let i : Nat := iInt.toNat
      pure (.nonposGePos i)
  | _ =>
      throw s!"unknown unsat_cert.kind: {kind}"

def exprVsConst? (op : CmpOp) (lhs rhs : Expr) : Option (Expr × CmpOp × Float) :=
  match rhs with
  | .const c => some (lhs, op, c)
  | _ =>
      match lhs with
      | .const c => some (rhs, swapCmp op, c)
      | _ => none

def verifyReason (p : Problem) (r : UnsatReason) : Except String Unit := do
  let some cmps := collectConjCmps p.formula
    | throw "unsat_cert only supports conjunctions of comparisons (no or/not)"
  let b := deriveBounds p cmps
  match r with
  | .boundsContradiction v _lo _hi =>
      match b.get? v with
      | none => throw s!"unsat_cert: unknown variable '{v}'"
      | some bb =>
          if bb.lo > bb.hi || (bb.lo == bb.hi && (bb.loStrict || bb.hiStrict)) then
            pure ()
          else
            throw "unsat_cert: no bound contradiction"
  | .nonnegLeNeg idx =>
      if idx ≥ cmps.size then
        throw "unsat_cert: cmp_index out of range"
      let (op, lhs, rhs) := cmps[idx]!
      let some (e, op', c) := exprVsConst? op lhs rhs
        | throw "unsat_cert: expected expr-vs-const comparison"
      if !(c < 0.0) then
        throw "unsat_cert: expected negative bound"
      match op' with
      | .le | .lt | .eq =>
          if exprNonneg b e then
            pure ()
          else
            throw "unsat_cert: expression not provably nonnegative"
      | _ =>
          throw "unsat_cert: expected <= / < / = after normalization"
  | .nonposGePos idx =>
      if idx ≥ cmps.size then
        throw "unsat_cert: cmp_index out of range"
      let (op, lhs, rhs) := cmps[idx]!
      let some (e, op', c) := exprVsConst? op lhs rhs
        | throw "unsat_cert: expected expr-vs-const comparison"
      if !(c > 0.0) then
        throw "unsat_cert: expected positive bound"
      match op' with
      | .ge | .gt | .eq =>
          if exprNonpos b e then
            pure ()
          else
            throw "unsat_cert: expression not provably nonpositive"
      | _ =>
          throw "unsat_cert: expected >= / > / = after normalization"

def tryCertify (p : Problem) : Option UnsatReason :=
  match collectConjCmps p.formula with
  | none => none
  | some cmps =>
      let bounds := deriveBounds p cmps
      let contradiction? :=
        bounds.toList.findSome? (fun (name, b) =>
          if b.lo > b.hi || (b.lo == b.hi && (b.loStrict || b.hiStrict)) then
            some (.boundsContradiction name b.lo b.hi)
          else
            none)
      match contradiction? with
      | some r => some r
      | none =>
          let indexed : Array (Nat × (CmpOp × Expr × Expr)) :=
            cmps.mapIdx (fun i c => (i, c))
          indexed.foldl
            (init := (none : Option UnsatReason))
            (fun acc (i, cmp) =>
              match acc with
              | some _ => acc
              | none =>
                  let (op, lhs, rhs) := cmp
                  match exprVsConst? op lhs rhs with
                  | none => none
                  | some (e, op', c) =>
                      if c < 0.0 then
                        match op' with
                        | .le | .lt | .eq =>
                            if exprNonneg bounds e then some (.nonnegLeNeg i) else none
                        | _ => none
                      else if c > 0.0 then
                        match op' with
                        | .ge | .gt | .eq =>
                            if exprNonpos bounds e then some (.nonposGePos i) else none
                        | _ => none
                      else
                        none)

end Unsat

end RealConstraints
end Computational
end HeytingLean
