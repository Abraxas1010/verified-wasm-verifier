import HeytingLean.ProgramCalculus.Futamura
import HeytingLean.ProgramCalculus.Instances.SKYBracket

/-!
# `futamura_sky_demo`

Repo-local Futamura-1 demo over the SKY/Bracket layer:

* Codes are closed SKY terms (`Comb`) (static input).
* Dynamic input is a closed SKY term (`Comb`).
* The interpreter program is `code · input` expressed as `Bracket.CExp`.
* Specialization substitutes `code` into the syntax, producing a residual `CExp` depending only on `input`.
-/

namespace HeytingLean.CLI.FutamuraSKYDemoMain

open HeytingLean
open HeytingLean.ProgramCalculus
open HeytingLean.ProgramCalculus.Instances
open HeytingLean.LoF
open HeytingLean.LoF.Combinators

private def die (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure 1

private def ok (b : Bool) (msg : String) : IO Unit := do
  if !b then
    throw (IO.userError msg)

private def okEq {α} [DecidableEq α] (x y : α) (msg : String) : IO Unit :=
  ok (decide (x = y)) msg

private def checkOne (fuel : Nat) (code x : Comb) : IO Unit := do
  let residual : Bracket.CExp SKYCI :=
    ProgramCalculus.compile (skyBracketMix fuel) (skyBracketInterpModel fuel) code
  IO.println s!"[sky] fuel={fuel} residual.size={Bracket.CExp.size residual}"
  IO.println s!"[sky] residual={reprStr residual}"

  -- Sanity: specializing should eliminate the `code` variable entirely.
  ok (decide (Bracket.CExp.occurs SKYCI.code residual = false)) "[sky] residual still mentions `code`"

  let dynamic : SKYCI → Comb
    | .code => Comb.K
    | .input => x
  let outResidual : Comb := SKYExec.reduceFuel fuel (Bracket.CExp.denote dynamic residual)
  let outSpec : Comb := skyBracketCodeSem fuel code x
  okEq outResidual outSpec s!"[sky] mismatch: got={reprStr outResidual} expected={reprStr outSpec}"

def main (_argv : List String) : IO UInt32 := do
  try
    let fuel := 12

    -- Identity: I · S ↦* S
    checkOne fuel Comb.I Comb.S

    -- Constant: (K · S) · K ↦* S
    checkOne fuel (Comb.app Comb.K Comb.S) Comb.K

    IO.println "futamura_sky_demo: ok"
    pure 0
  catch e =>
    die s!"futamura_sky_demo: FAILED: {e}"

end HeytingLean.CLI.FutamuraSKYDemoMain

open HeytingLean.CLI.FutamuraSKYDemoMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.FutamuraSKYDemoMain.main args
