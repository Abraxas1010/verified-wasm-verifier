import Lean.Data.Json
import Init.Data.Rat
import Std.Data.HashMap
import HeytingLean.Computational.RealConstraints.UnsatInterval

namespace HeytingLean
namespace Computational
namespace RealConstraints

open Lean
open Lean.Json

namespace RatCheck

abbrev RatEnv := Std.HashMap String Rat

private def ratOfJsonNumber (n : JsonNumber) : Rat :=
  mkRat n.mantissa (10 ^ n.exponent)

private def ratOfSlashString (s : String) : Except String Rat := do
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
  pure (mkRat num den)

def ratOfJson (j : Json) : Except String Rat := do
  match j with
  | .num n => pure (ratOfJsonNumber n)
  | .str s =>
      match Json.parse s.trim with
      | .ok (.num n) => pure (ratOfJsonNumber n)
      | _ => ratOfSlashString s
  | .obj _ =>
      -- Support the `{ "num": <int>, "den": <nat> }` encoding used elsewhere in `UnsatInterval`.
      UnsatInterval.ratOfJson j
  | _ =>
      throw "expected rational number"

def envOfJsonObj (j : Json) : Except String RatEnv := do
  let obj ← j.getObj?
  let mut env : RatEnv := {}
  for (k, v) in obj.toList do
    env := env.insert k (← ratOfJson v)
  pure env

private def checkBounds (p : UnsatInterval.RatIR.Problem) (env : RatEnv) : Except String Unit := do
  for v in p.vars.toList do
    match env.get? v.name with
    | none => throw s!"missing witness value for variable '{v.name}'"
    | some x =>
        if x < v.lo then
          throw s!"variable '{v.name}' below lower bound"
        if x > v.hi then
          throw s!"variable '{v.name}' above upper bound"
  pure ()

def checkSatWitnessExact (problemJson : Json) (env : RatEnv) : Except String Bool := do
  let p ← UnsatInterval.RatIR.Problem.ofJson problemJson
  checkBounds p env
  let mut envI : UnsatInterval.Env := {}
  for (k, v) in env.toList do
    envI := envI.insert k { lo := v, hi := v }
  match ← UnsatInterval.RatIR.Formula.evalTri envI p.formula with
  | .tt => pure true
  | .ff => pure false
  | .unknown => throw "exact check: formula evaluated to unknown (unexpected at a point witness)"

end RatCheck

end RealConstraints
end Computational
end HeytingLean
