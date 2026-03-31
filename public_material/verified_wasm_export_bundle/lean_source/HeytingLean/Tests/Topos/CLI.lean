import HeytingLean.Tests.Topos.Scaffold
import HeytingLean.Tests.Topos.PresheafSmoke
import HeytingLean.Tests.Topos.SheafNeuralNetSmoke

namespace HeytingLean
namespace Tests
namespace Topos

structure RunConfig where
  readPath? : Option String := none
  requireEnv? : Option String := none
  spawnCmd? : Option String := none
  help : Bool := false
deriving Inhabited

private def parseArgs (args : List String) : RunConfig :=
  let rec loop (cfg : RunConfig) (xs : List String) : RunConfig :=
    match xs with
    | [] => cfg
    | "-h" :: rest => loop { cfg with help := true } rest
    | "--help" :: rest => loop { cfg with help := true } rest
    | "--read" :: p :: rest => loop { cfg with readPath? := some p } rest
    | "--require-env" :: k :: rest => loop { cfg with requireEnv? := some k } rest
    | "--spawn" :: c :: rest => loop { cfg with spawnCmd? := some c } rest
    | _ :: rest => loop cfg rest
  loop {} args

private def runRead (path : String) : IO (Option UInt32) := do
  try
    let _ ← IO.FS.readFile path
    pure none
  catch e =>
    IO.eprintln s!"[robustness-io] failed to read '{path}': {e.toString}"
    pure (some 3)

private def runRequireEnv (key : String) : IO (Option UInt32) := do
  let v ← IO.getEnv key
  match v with
  | some _ => pure none
  | none =>
    IO.eprintln s!"[robustness-env] missing env '{key}'"
    pure (some 4)

private def runSpawn (cmd : String) : IO (Option UInt32) := do
  try
    let child ← IO.Process.spawn { cmd := cmd, args := #[] }
    let ec ← child.wait
    if ec == 0 then pure none else pure (some ec)
  catch e =>
    IO.eprintln s!"[robustness-subprocess] failed to spawn '{cmd}': {e.toString}"
    pure (some 5)

end Topos
end Tests
end HeytingLean

def main (args : List String) : IO UInt32 := do
  let cfg := HeytingLean.Tests.Topos.parseArgs args
  if cfg.help then
    IO.println "topos_tests [--read PATH] [--require-env KEY] [--spawn CMD]"
    IO.println "  --read PATH        attempt to read PATH; exit 3 on failure"
    IO.println "  --require-env KEY  require env var KEY; exit 4 if missing"
    IO.println "  --spawn CMD        spawn CMD; return its exit or 5 on spawn error"
    return 0
  let mut exitCode : UInt32 := 0
  match cfg.readPath? with
  | some p =>
    match (← HeytingLean.Tests.Topos.runRead p) with
    | some n => exitCode := max exitCode n
    | none => pure ()
  | none => pure ()
  match cfg.requireEnv? with
  | some k =>
    match (← HeytingLean.Tests.Topos.runRequireEnv k) with
    | some n => exitCode := max exitCode n
    | none => pure ()
  | none => pure ()
  match cfg.spawnCmd? with
  | some c =>
    match (← HeytingLean.Tests.Topos.runSpawn c) with
    | some n => exitCode := max exitCode n
    | none => pure ()
  | none => pure ()
  pure exitCode
