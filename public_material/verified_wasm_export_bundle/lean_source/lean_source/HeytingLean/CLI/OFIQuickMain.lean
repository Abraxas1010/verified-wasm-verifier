import Lean
import Mathlib.Data.Set.Lattice

open Lean

structure QArgs where
  target : String := "alpha+beta"
  deriving Inhabited

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x::y::rest => if x = flag then some y else parseArg (y::rest) flag
  | _ => none

private def splitTarget (s : String) : List String :=
  s.splitOn "+" |>.map (·.trim) |>.filter (· ≠ "")

private def splitComma (s : String) : List String :=
  s.splitOn "," |>.map (·.trim) |>.filter (· ≠ "")

private def quickOFI (tokens : List String) : Nat :=
  if tokens.isEmpty then 0 else tokens.length - 1

/-! Compute a concrete OFI-like index using a simple set nucleus.
We take the universe as `Set String`, the nucleus `S ↦ S ∪ U` with
`U = {"alpha"}`, and the initial element as the set of target tokens.
Then `R` stabilizes in 0 steps if "alpha" is already present; otherwise 1. -/
private def listToSet (xs : List String) : Set String := fun s => s ∈ xs

private def setOFI (tokens : List String) (uAtoms : List String) : Nat :=
  -- For addClosure with universe U, stabilization is 0 iff U ⊆ tokens; else 1 (or 0 if U = ∅).
  if uAtoms = [] then 0
  else if uAtoms.all (fun a => tokens.contains a) then 0 else 1

def main (argv : List String) : IO Unit := do
  let tgt := (parseArg argv "--target").getD "alpha+beta"
  let toks := splitTarget tgt
  let uStr := (parseArg argv "--U").getD "alpha"
  let uAtoms := splitComma uStr
  let idx := quickOFI toks
  let missing := uAtoms.filter (fun a => !(toks.contains a))
  let j := Json.mkObj
    [ ("mode", Json.str "quick-ofi")
    , ("target", Json.arr (toks.toArray.map Json.str))
    , ("U", Json.arr (uAtoms.toArray.map Json.str))
    , ("ofiIndex", Json.num idx)
    , ("ofiIndexSet", Json.num (setOFI toks uAtoms))
    , ("missing", Json.arr (missing.toArray.map Json.str))
    , ("stable", Json.bool true) ]
  IO.println j.pretty
