import Lean
import HeytingLean.CLI.Args
import HeytingLean.LoF.Combinators.Lambda.Ruliology

open Lean

namespace HeytingLean
namespace CLI

open HeytingLean.LoF.Combinators
open HeytingLean.LoF.Combinators.Lambda

/-!
CLI: bounded multiway exploration for untyped λ-terms (de Bruijn)

This mirrors `sky_multiway_demo` but uses the β multiway relation defined in:
`HeytingLean.LoF.Combinators.Lambda.Beta`.
-/

namespace LambdaMultiway

abbrev LTerm := HeytingLean.LoF.Combinators.Lambda.Term

structure Args where
  demo : String := "Omega"
  maxDepth : Nat := 4
deriving Inhabited

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x :: y :: rest => if x = flag then some y else parseArg (y :: rest) flag
  | _ => none

private def parseArgs (argv : List String) : Args :=
  let argv := HeytingLean.CLI.stripLakeArgs argv
  let demo := (parseArg argv "--demo").getD "Omega"
  let maxDepth := (parseArg argv "--maxDepth").bind (·.toNat?) |>.getD 4
  { demo, maxDepth }

/-! ## Demo terms -/

private def demoId : LTerm :=
  .lam (.var 0)

private def demoOmega : LTerm :=
  -- ω := λx. x x  (de Bruijn: λ. 0 0)
  .lam (.app (.var 0) (.var 0))

private def demoBigOmega : LTerm :=
  -- Ω := ω ω  (diverges)
  .app demoOmega demoOmega

private def selectDemo (name : String) : (String × LTerm) :=
  let key := name.trim.toLower
  if key = "id" then
    ("lambda_id", demoId)
  else if key = "omega" || key = "ω" then
    ("lambda_omega", demoOmega)
  else if key = "k" then
    ("lambda_k", Lambda.Term.KEnc)
  else if key = "s" then
    ("lambda_s", Lambda.Term.SEnc)
  else if key = "y" then
    ("lambda_y", Lambda.Term.YEnc)
  else
    ("lambda_omegaomega", demoBigOmega)

def main (argv : List String) : IO Unit := do
  let args := parseArgs argv
  let (sysName, init) := selectDemo args.demo
  let payload := Lambda.buildMultiwayJson sysName init args.maxDepth
  IO.println payload.pretty

end LambdaMultiway

end CLI
end HeytingLean

def main (argv : List String) : IO Unit :=
  HeytingLean.CLI.LambdaMultiway.main argv
