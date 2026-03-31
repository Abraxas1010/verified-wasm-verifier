import HeytingLean.LoF.Combinators.STLC
import HeytingLean.LoF.Combinators.STLCSKY

/-!
# lof_stlc_demo (Phase 5)

Executable demo: run a tiny STLC type checker both:
1) directly in Lean (`STLC.check`), and
2) as a SKY combinator program compiled via bracket abstraction (`STLCSKY.runCheckFuel`),

and cross-check the results on a small suite of examples.
-/

namespace HeytingLean.CLI.LoFSTLCDemoMain

open HeytingLean.LoF.Combinators

private def usage : String :=
  String.intercalate "\n"
    [ "Usage: lof_stlc_demo [--fuel N]"
    , ""
    , "Runs a tiny STLC checker compiled to SKY and cross-checks it against Lean."
    , ""
    , "Options:"
    , "  --fuel N   Reduction fuel (default: 2000)"
    , "  --help     Show this help"
    ]

private def die (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure code

private def parseArgs (argv : List String) : IO Nat := do
  match argv with
  | [] => pure 2000
  | ["--help"] =>
      IO.println usage
      throw (IO.userError "help")
  | ["--fuel", nStr] =>
      match nStr.toNat? with
      | some n => pure n
      | none => throw <| IO.userError s!"invalid --fuel value: {nStr}"
  | _ =>
      throw <| IO.userError s!"invalid arguments\n\n{usage}"

private def okEq {α} [DecidableEq α] (x y : α) (msg : String) : IO Unit := do
  if decide (x = y) then
    pure ()
  else
    throw (IO.userError msg)

private def runOne (fuel : Nat) (Γ : STLC.Ctx) (t : STLC.Term) (ty : STLC.Ty) : IO Unit := do
  let leanRes := STLC.check Γ t ty
  match STLCSKY.runCheckFuel fuel Γ t ty with
  | none =>
      throw <| IO.userError s!"SKY checker failed to produce a boolean (fuel={fuel}).\nterm={reprStr t}\nctx={reprStr Γ}\nty={reprStr ty}"
  | some skyRes =>
      okEq skyRes leanRes s!"Mismatch (fuel={fuel}).\nterm={reprStr t}\nctx={reprStr Γ}\nty={reprStr ty}\nLean={leanRes}\nSKY={skyRes}"

def main (argv : List String) : IO UInt32 := do
  try
    let fuel ← parseArgs argv

    -- Closed terms (no context).
    runOne fuel [] STLC.tIdBool (STLC.Ty.bool ⟶ STLC.Ty.bool)
    runOne fuel [] STLC.tConstBool (STLC.Ty.bool ⟶ (STLC.Ty.bool ⟶ STLC.Ty.bool))
    runOne fuel [] STLC.tAppIdTrue STLC.Ty.bool
    runOne fuel [] STLC.tBadApp STLC.Ty.bool

    -- Variable lookup sanity.
    runOne fuel [STLC.Ty.bool] (.var 0) STLC.Ty.bool
    runOne fuel [] (.var 0) STLC.Ty.bool

    IO.println "lof_stlc_demo: ok"
    pure 0
  catch e =>
    match e with
    | .userError "help" => pure 0
    | _ => die 1 s!"lof_stlc_demo: FAILED: {e}"

end HeytingLean.CLI.LoFSTLCDemoMain

open HeytingLean.CLI.LoFSTLCDemoMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.LoFSTLCDemoMain.main args

