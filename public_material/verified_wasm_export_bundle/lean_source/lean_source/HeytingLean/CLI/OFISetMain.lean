import Lean
import Mathlib.Data.Set.Lattice

open Lean

namespace HeytingLean
namespace CLI

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x::y::rest => if x = flag then some y else parseArg (y::rest) flag
  | _ => none

private def splitPlus (s : String) : List String :=
  s.splitOn "+" |>.map (·.trim) |>.filter (· ≠ "")

private def splitComma (s : String) : List String :=
  s.splitOn "," |>.map (·.trim) |>.filter (· ≠ "")

private def listToSet (xs : List String) : Set String := fun t => t ∈ xs

def main (argv : List String) : IO Unit := do
  let tgt  := (parseArg argv "--target").getD ""
  let ustr := (parseArg argv "--U").getD ""
  let cutoff := (parseArg argv "--cutoff").bind (·.toNat?) |>.getD 32
  let toks := splitPlus tgt
  let atoms := splitComma ustr
  let X : Set String := listToSet toks
  let U : Set String := listToSet atoms
  -- For addClosure, stabilization is 0 iff U ⊆ X, otherwise 1 when U ≠ ∅ (else 0 if U = ∅).
  let uSub : Bool := atoms.all (fun a => toks.contains a)
  let idx := if uSub then 0 else (if atoms = [] then 0 else 1)
  let j := Json.mkObj
    [ ("mode", Json.str "ofi-set")
    , ("target", Json.arr (toks.toArray.map Json.str))
    , ("U", Json.arr (atoms.toArray.map Json.str))
    , ("cutoff", Json.num cutoff)
    , ("ofiIndexSet", Json.num idx) ]
  IO.println j.pretty

end CLI
end HeytingLean
