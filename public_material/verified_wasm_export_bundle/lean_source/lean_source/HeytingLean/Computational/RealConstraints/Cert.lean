import Lean
import Lean.Data.Json
import Std.Data.HashMap
import HeytingLean.Computational.RealConstraints.IR

namespace HeytingLean
namespace Computational
namespace RealConstraints

open Lean
open Lean.Json

namespace Cert

def jsonOfFloat (x : Float) : Json :=
  match JsonNumber.fromFloat? x with
  | .inr n => Json.num n
  | .inl s => Json.str s

private def floatOfSlashString (s : String) : Except String Float := do
  let parts := s.trim.splitOn "/"
  if parts.length != 2 then
    throw "expected rational string 'num/den'"
  let numStr := parts[0]!.trim
  let denStr := parts[1]!.trim
  let num ←
    match numStr.toInt? with
    | some n => pure n
    | none => throw "expected integer numerator in 'num/den'"
  let den ←
    match denStr.toNat? with
    | some n => pure n
    | none => throw "expected natural denominator in 'num/den'"
  if den == 0 then
    throw "denominator must be positive"
  pure (Float.ofInt num / Float.ofNat den)

private def floatOfJson (j : Json) : Except String Float := do
  match j with
  | .num n => pure n.toFloat
  | .str s =>
      match Json.parse s.trim with
      | .ok (.num n) => pure n.toFloat
      | _ => floatOfSlashString s
  | _ => throw "expected number"

def envOfJsonObj (j : Json) : Except String Env := do
  let obj ← j.getObj?
  let mut env : Env := {}
  for (k, v) in obj.toList do
    match floatOfJson v with
    | .ok x => env := env.insert k x
    | .error _ => throw s!"env[{k}] not a number"
  pure env

def envToJsonObj (env : Env) : Json :=
  let fields := env.toList.map (fun (k, v) => (k, jsonOfFloat v))
  Json.mkObj fields

def midsFromDRealModel (j : Json) : Except String Env := do
  let obj ← j.getObj?
  let mut env : Env := {}
  for (k, v) in obj.toList do
    let o ← v.getObj?
    match o.get? "mid" with
    | some midJ =>
        match midJ.getNum? with
        | .ok n => env := env.insert k n.toFloat
        | .error _ => throw s!"model[{k}].mid not a number"
    | none => throw s!"model[{k}] missing field 'mid'"
  pure env

def checkBounds (p : Problem) (env : Env) (eps : Float) : Except String Unit := do
  for v in p.vars.toList do
    match env.get? v.name with
    | none => throw s!"missing witness value for variable '{v.name}'"
    | some x =>
        if x + eps < v.lo then
          throw s!"variable '{v.name}' below lower bound"
        if x > v.hi + eps then
          throw s!"variable '{v.name}' above upper bound"
  pure ()

def checkSatWitness (p : Problem) (env : Env) (eps : Float) : Except String Bool := do
  checkBounds p env eps
  Formula.eval env eps p.formula

end Cert

end RealConstraints
end Computational
end HeytingLean
