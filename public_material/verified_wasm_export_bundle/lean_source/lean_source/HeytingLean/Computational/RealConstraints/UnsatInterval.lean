import Lean.Data.Json
import Init.Data.Rat
import Std.Data.HashMap
import HeytingLean.Computational.RealConstraints.IR

namespace HeytingLean
namespace Computational
namespace RealConstraints

open Lean
open Lean.Json

namespace UnsatInterval

namespace RatIR

structure VarDecl where
  name : String
  lo : Rat
  hi : Rat
deriving Repr, Inhabited

inductive Expr where
  | var (name : String)
  | const (value : Rat)
  | add (children : Array Expr)
  | mul (children : Array Expr)
  | neg (child : Expr)
  | pow (base : Expr) (exp : Nat)
deriving Repr, Inhabited

inductive Formula where
  | and (children : Array Formula)
  | or (children : Array Formula)
  | not (child : Formula)
  | cmp (op : CmpOp) (lhs : Expr) (rhs : Expr)
deriving Repr, Inhabited

structure Problem where
  vars : Array VarDecl
  formula : Formula
deriving Repr, Inhabited

private def ratOfJsonNumber (n : JsonNumber) : Rat :=
  mkRat n.mantissa (10 ^ n.exponent)

namespace JsonParse

private def expectObj (j : Json) : Except String Json := do
  match j.getObj? with
  | .ok _ => pure j
  | .error _ => throw "expected JSON object"

private def getStr (obj : Json) (k : String) : Except String String := do
  match obj.getObjVal? k with
  | .ok v =>
      match v.getStr? with
      | .ok s => pure s
      | .error _ => throw s!"field '{k}' not a string"
  | .error _ => throw s!"missing field '{k}'"

private def getNumRat (obj : Json) (k : String) : Except String Rat := do
  match obj.getObjVal? k with
  | .ok v =>
      match v.getNum? with
      | .ok n => pure (ratOfJsonNumber n)
      | .error _ => throw s!"field '{k}' not a number"
  | .error _ => throw s!"missing field '{k}'"

private def getNat (obj : Json) (k : String) : Except String Nat := do
  match obj.getObjVal? k with
  | .ok v =>
      match v.getInt? with
      | .ok i =>
          if i < 0 then
            throw s!"field '{k}' must be nonnegative"
          else
            pure i.toNat
      | .error _ => throw s!"field '{k}' not an integer"
  | .error _ => throw s!"missing field '{k}'"

private def getArr (obj : Json) (k : String) : Except String (Array Json) := do
  match obj.getObjVal? k with
  | .ok (Json.arr xs) => pure xs
  | .ok _ => throw s!"field '{k}' not an array"
  | .error _ => throw s!"missing field '{k}'"

private def getObjValOpt (obj : Json) (k : String) : Option Json :=
  match obj.getObjVal? k with
  | .ok v => some v
  | .error _ => none

end JsonParse

namespace VarDecl

def ofJson (j : Json) : Except String VarDecl := do
  let obj ← JsonParse.expectObj j
  let name ← JsonParse.getStr obj "name"
  let lo ← JsonParse.getNumRat obj "lo"
  let hi ← JsonParse.getNumRat obj "hi"
  if lo > hi then
    throw s!"var '{name}': lo > hi"
  pure { name, lo, hi }

end VarDecl

namespace Expr

partial def ofJson (j : Json) : Except String Expr := do
  let obj ← JsonParse.expectObj j
  let kind ← JsonParse.getStr obj "kind"
  match kind with
  | "var" =>
      let name ← JsonParse.getStr obj "name"
      pure (.var name)
  | "const" =>
      let v ← JsonParse.getNumRat obj "value"
      pure (.const v)
  | "add" =>
      let xs ← JsonParse.getArr obj "children"
      let mut out : Array Expr := #[]
      for x in xs do
        out := out.push (← Expr.ofJson x)
      pure (.add out)
  | "mul" =>
      let xs ← JsonParse.getArr obj "children"
      let mut out : Array Expr := #[]
      for x in xs do
        out := out.push (← Expr.ofJson x)
      pure (.mul out)
  | "neg" =>
      match JsonParse.getObjValOpt obj "child" with
      | none => throw "expr.neg missing field 'child'"
      | some ch => pure (.neg (← Expr.ofJson ch))
  | "pow" =>
      let base ←
        match JsonParse.getObjValOpt obj "base" with
        | none => throw "expr.pow missing field 'base'"
        | some b => Expr.ofJson b
      let exp ← JsonParse.getNat obj "exp"
      pure (.pow base exp)
  | _ =>
      throw s!"unknown expr kind: {kind}"

end Expr

namespace Formula

private def opOfString? (s : String) : Option CmpOp :=
  match s with
  | "<" => some .lt
  | "<=" => some .le
  | "=" => some .eq
  | "==" => some .eq
  | ">=" => some .ge
  | ">" => some .gt
  | _ => none

partial def ofJson (j : Json) : Except String Formula := do
  let obj ← JsonParse.expectObj j
  let kind ← JsonParse.getStr obj "kind"
  match kind with
  | "and" =>
      let xs ← JsonParse.getArr obj "children"
      let mut out : Array Formula := #[]
      for x in xs do
        out := out.push (← Formula.ofJson x)
      pure (.and out)
  | "or" =>
      let xs ← JsonParse.getArr obj "children"
      let mut out : Array Formula := #[]
      for x in xs do
        out := out.push (← Formula.ofJson x)
      pure (.or out)
  | "not" =>
      match JsonParse.getObjValOpt obj "child" with
      | none => throw "formula.not missing field 'child'"
      | some ch => pure (.not (← Formula.ofJson ch))
  | "cmp" =>
      let opStr ← JsonParse.getStr obj "op"
      let some op := opOfString? opStr
        | throw s!"formula.cmp: unsupported op '{opStr}'"
      let lhs ←
        match JsonParse.getObjValOpt obj "lhs" with
        | none => throw "formula.cmp missing field 'lhs'"
        | some e => Expr.ofJson e
      let rhs ←
        match JsonParse.getObjValOpt obj "rhs" with
        | none => throw "formula.cmp missing field 'rhs'"
        | some e => Expr.ofJson e
      pure (.cmp op lhs rhs)
  | _ =>
      throw s!"unknown formula kind: {kind}"

end Formula

namespace Problem

def ofJson (j : Json) : Except String Problem := do
  let obj ← JsonParse.expectObj j
  let varsJ ← JsonParse.getArr obj "vars"
  let mut vars : Array VarDecl := #[]
  for v in varsJ do
    vars := vars.push (← VarDecl.ofJson v)
  let formulaJ ←
    match obj.getObjVal? "formula" with
    | .ok v => pure v
    | .error _ => throw "missing field 'formula'"
  let formula ← Formula.ofJson formulaJ
  pure { vars, formula }

end Problem

end RatIR

structure Interval where
  lo : Rat
  hi : Rat
deriving Repr, Inhabited

abbrev Env := Std.HashMap String Interval

inductive Tri where
  | tt
  | ff
  | unknown
deriving Repr, Inhabited, DecidableEq

namespace Tri

def not : Tri → Tri
  | .tt => .ff
  | .ff => .tt
  | .unknown => .unknown

def and : Tri → Tri → Tri
  | .ff, _ => .ff
  | _, .ff => .ff
  | .tt, .tt => .tt
  | _, _ => .unknown

def or : Tri → Tri → Tri
  | .tt, _ => .tt
  | _, .tt => .tt
  | .ff, .ff => .ff
  | _, _ => .unknown

end Tri

private def minRat (a b : Rat) : Rat := if a ≤ b then a else b
private def maxRat (a b : Rat) : Rat := if a ≤ b then b else a

private def intervalConst (x : Rat) : Interval := { lo := x, hi := x }

private def intervalAdd (a b : Interval) : Interval :=
  { lo := a.lo + b.lo, hi := a.hi + b.hi }

private def intervalNeg (a : Interval) : Interval :=
  { lo := -a.hi, hi := -a.lo }

private def intervalMul (a b : Interval) : Interval :=
  let xs : Array Rat := #[a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi]
  let lo := xs.foldl minRat xs[0]!
  let hi := xs.foldl maxRat xs[0]!
  { lo, hi }

private def intervalPow (a : Interval) (n : Nat) : Interval :=
  Nat.rec (motive := fun _ => Interval) (intervalConst 1) (fun _ acc => intervalMul acc a) n

namespace RatIR.Expr

partial def evalInterval (env : Env) : RatIR.Expr → Except String Interval
  | .var name =>
      match env.get? name with
      | some i => pure i
      | none => throw s!"unbound variable: {name}"
  | .const v => pure (intervalConst v)
  | .add xs =>
      xs.foldlM (init := intervalConst 0) (fun acc e => do
        pure (intervalAdd acc (← evalInterval env e)))
  | .mul xs =>
      xs.foldlM (init := intervalConst 1) (fun acc e => do
        pure (intervalMul acc (← evalInterval env e)))
  | .neg e => do
      pure (intervalNeg (← evalInterval env e))
  | .pow b n => do
      pure (intervalPow (← evalInterval env b) n)

end RatIR.Expr

namespace RatIR.Formula

def collectConjCmps : RatIR.Formula → Option (Array (CmpOp × RatIR.Expr × RatIR.Expr))
  | .cmp op lhs rhs => some #[(op, lhs, rhs)]
  | .and xs =>
      xs.foldl
        (init := some (#[] : Array (CmpOp × RatIR.Expr × RatIR.Expr)))
        (fun acc f =>
          match acc, collectConjCmps f with
          | some a, some b => some (a ++ b)
          | _, _ => none)
  | _ => none

end RatIR.Formula

private def cmpRefutedByIntervals (op : CmpOp) (lhs rhs : Interval) : Bool :=
  match op with
  | .le => lhs.lo > rhs.hi
  | .lt => lhs.lo ≥ rhs.hi
  | .ge => lhs.hi < rhs.lo
  | .gt => lhs.hi ≤ rhs.lo
  | .eq => lhs.hi < rhs.lo || rhs.hi < lhs.lo

inductive CertTree where
  | closed
  | refute (cmpIndex : Nat)
  | split (var : String) (midNum : Int) (midDen : Nat) (left right : CertTree)
deriving Repr, Inhabited

private def midOf (num : Int) (den : Nat) : Except String Rat :=
  if den = 0 then
    throw "mid.den must be nonzero"
  else
    pure (mkRat num den)

def jsonOfRat (q : Rat) : Json :=
  Json.mkObj
    [ ("num", Json.num (JsonNumber.fromInt q.num))
    , ("den", Json.num (JsonNumber.fromNat q.den))
    ]

def ratOfJson (j : Json) : Except String Rat := do
  let obj ← j.getObj?
  let numJ ←
    match obj.get? "num" with
    | some v => pure v
    | none => throw "rat.num missing"
  let denJ ←
    match obj.get? "den" with
    | some v => pure v
    | none => throw "rat.den missing"
  let numInt : Int ←
    match numJ with
    | .num n =>
        if n.exponent != 0 then
          throw "rat.num must be an integer"
        else
          pure n.mantissa
    | _ => throw "rat.num must be a JSON number"
  let denNat : Nat ←
    match denJ with
    | .num n =>
        if n.exponent != 0 then
          throw "rat.den must be an integer"
        else if n.mantissa <= 0 then
          throw "rat.den must be positive"
        else
          pure n.mantissa.toNat
    | _ => throw "rat.den must be a JSON number"
  pure (mkRat numInt denNat)

def CertTree.toJson : CertTree → Json
  | .closed =>
      Json.mkObj
        [ ("kind", Json.str "closed")
        ]
  | .refute i =>
      Json.mkObj
        [ ("kind", Json.str "refute")
        , ("cmp_index", Json.num (JsonNumber.fromNat i))
        ]
  | .split v midNum den l r =>
      Json.mkObj
        [ ("kind", Json.str "split")
        , ("var", Json.str v)
        , ("mid", Json.mkObj [("num", Json.num (JsonNumber.fromInt midNum)), ("den", Json.num (JsonNumber.fromNat den))])
        , ("left", CertTree.toJson l)
        , ("right", CertTree.toJson r)
        ]

partial def CertTree.ofJson (j : Json) : Except String CertTree := do
  let obj ← j.getObj?
  let kind ←
    match obj.get? "kind" with
    | some (.str s) => pure s
    | _ => throw "cert.kind missing/invalid"
  match kind with
  | "closed" =>
      pure .closed
  | "refute" =>
      let iJ := obj.get? "cmp_index" |>.getD Json.null
      let iInt ←
        match iJ.getInt? with
        | .ok k => pure k
        | .error _ => throw "cert.refute.cmp_index missing/invalid"
      if iInt < 0 then throw "cert.refute.cmp_index must be nonnegative"
      pure (.refute iInt.toNat)
  | "split" =>
      let v ←
        match obj.get? "var" with
        | some (.str s) => pure s
        | _ => throw "cert.split.var missing/invalid"
      let midJ := obj.get? "mid" |>.getD Json.null
      let mid ← ratOfJson midJ
      let lJ := obj.get? "left" |>.getD Json.null
      let rJ := obj.get? "right" |>.getD Json.null
      let l ← CertTree.ofJson lJ
      let r ← CertTree.ofJson rJ
      pure (.split v mid.num mid.den l r)
  | _ =>
      throw s!"unknown cert.kind: {kind}"

private def envOfProblem (p : RatIR.Problem) : Env :=
  p.vars.foldl (init := ({} : Env)) (fun acc v => acc.insert v.name { lo := v.lo, hi := v.hi })

private def splitEnv (env : Env) (var : String) (mid : Rat) : Except String (Env × Env) := do
  match env.get? var with
  | none => throw s!"split: unknown variable '{var}'"
  | some i =>
      if !(i.lo < mid && mid < i.hi) then
        throw "split: mid must be strictly inside the current interval"
      let left := env.insert var { lo := i.lo, hi := mid }
      let right := env.insert var { lo := mid, hi := i.hi }
      pure (left, right)

private def cmpTri (op : CmpOp) (lhs rhs : Interval) : Tri :=
  match op with
  | .le =>
      if lhs.hi ≤ rhs.lo then .tt
      else if lhs.lo > rhs.hi then .ff
      else .unknown
  | .lt =>
      if lhs.hi < rhs.lo then .tt
      else if lhs.lo ≥ rhs.hi then .ff
      else .unknown
  | .ge =>
      if lhs.lo ≥ rhs.hi then .tt
      else if lhs.hi < rhs.lo then .ff
      else .unknown
  | .gt =>
      if lhs.lo > rhs.hi then .tt
      else if lhs.hi ≤ rhs.lo then .ff
      else .unknown
  | .eq =>
      if lhs.lo = lhs.hi && rhs.lo = rhs.hi && lhs.lo = rhs.lo then
        .tt
      else if lhs.hi < rhs.lo || rhs.hi < lhs.lo then
        .ff
      else
        .unknown

namespace RatIR.Formula

partial def evalTri (env : Env) : RatIR.Formula → Except String Tri
  | .and xs =>
      xs.foldlM (init := Tri.tt) (fun acc f => do pure (Tri.and acc (← evalTri env f)))
  | .or xs =>
      xs.foldlM (init := Tri.ff) (fun acc f => do pure (Tri.or acc (← evalTri env f)))
  | .not f => do
      pure (Tri.not (← evalTri env f))
  | .cmp op lhs rhs => do
      let lhsI ← RatIR.Expr.evalInterval env lhs
      let rhsI ← RatIR.Expr.evalInterval env rhs
      pure (cmpTri op lhsI rhsI)

end RatIR.Formula

def verify (problemJson : Json) (cert : CertTree) : Except String Unit := do
  let p ← RatIR.Problem.ofJson problemJson
  let cmpsOpt := RatIR.Formula.collectConjCmps p.formula
  let rec go (env : Env) (c : CertTree) : Except String Unit := do
    match c with
    | .closed =>
        match ← RatIR.Formula.evalTri env p.formula with
        | .ff => pure ()
        | .tt => throw "cert.closed: formula is true on this box"
        | .unknown => throw "cert.closed: formula not refuted (unknown)"
    | .refute idx =>
        let some cmps := cmpsOpt
          | throw "cert.refute only supported for conjunctions of comparisons (no or/not)"
        if idx ≥ cmps.size then
          throw "cert.refute: cmp_index out of range"
        let (op, lhs, rhs) := cmps[idx]!
        let lhsI ← RatIR.Expr.evalInterval env lhs
        let rhsI ← RatIR.Expr.evalInterval env rhs
        if cmpRefutedByIntervals op lhsI rhsI then
          pure ()
        else
          throw "cert.refute: comparison not refuted by interval evaluation"
    | .split var midNum den left right =>
        let mid ← midOf midNum den
        let (envL, envR) ← splitEnv env var mid
        go envL left
        go envR right
  go (envOfProblem p) cert

private def chooseSplitVar (vars : Array RatIR.VarDecl) (env : Env) : Option String :=
  vars.foldl
    (init := (none : Option (String × Rat)))
    (fun acc v =>
      match env.get? v.name with
      | none => acc
      | some i =>
          let w := i.hi - i.lo
          if w ≤ 0 then
            acc
          else
            match acc with
            | none => some (v.name, w)
            | some (_, w0) => if w > w0 then some (v.name, w) else acc)
    |>.map (·.1)

def tryCertify (problemJson : Json) (maxDepth : Nat := 10) : Except String (Option CertTree) := do
  let p ← RatIR.Problem.ofJson problemJson
  let rec go (env : Env) (depth : Nat) : Option CertTree :=
    match RatIR.Formula.evalTri env p.formula with
    | .error _ => none
    | .ok .ff => some .closed
    | .ok .tt => none
    | .ok .unknown =>
        match depth with
        | 0 => none
        | depth + 1 =>
            match chooseSplitVar p.vars env with
            | none => none
            | some v =>
                match env.get? v with
                | none => none
                | some i =>
                    let mid := (i.lo + i.hi) / 2
                    if !(i.lo < mid && mid < i.hi) then
                      none
                    else
                      let envL := env.insert v { lo := i.lo, hi := mid }
                      let envR := env.insert v { lo := mid, hi := i.hi }
                      match go envL depth, go envR depth with
                      | some l, some r => some (.split v mid.num mid.den l r)
                      | _, _ => none
  pure (go (envOfProblem p) maxDepth)

end UnsatInterval

end RealConstraints
end Computational
end HeytingLean
