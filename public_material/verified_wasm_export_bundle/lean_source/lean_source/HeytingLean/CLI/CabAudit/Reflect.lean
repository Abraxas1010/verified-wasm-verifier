import Lean
open Lean

def allow (n : Name) : Bool :=
  n == Name.str Name.anonymous "propext" ||
  n == Name.str Name.anonymous "funext" ||
  n.toString == "Quot.sound" ||
  n.toString == "Classical.choice"

def nameStartsWith (n : Name) (pref : String) : Bool := n.toString.startsWith pref

def moduleOf (n : Name) : String :=
  String.intercalate "/" (n.components.dropLast.map Name.toString)

def collectAxiomsFor (n : Name) : CoreM (List Name) := do
  let used ← Lean.collectAxioms n
  return used.toList

def runReflect (pref : String) : CoreM String := do
  let env ← getEnv
  let consts := env.constants.toList.map Prod.fst |>.filter (fun n => nameStartsWith n pref)
  let mut arr : Array Json := #[]
  for n in consts do
    let used ← collectAxiomsFor n
    let bad := used.filter (fun a => !(allow a))
    let j := Json.mkObj [
      ("name", Json.str n.toString),
      ("module", Json.str (moduleOf n)),
      ("axioms", Json.arr <| used.toArray.map (fun x => Json.str x.toString)),
      ("allowlist_ok", Json.bool bad.isEmpty),
      ("bad", Json.arr <| bad.toArray.map (fun x => Json.str x.toString))
    ]
    arr := arr.push j
  let out := Json.mkObj [("implemented", Json.bool true), ("results", Json.arr arr)]
  return out.compress

def setupSearchPath : IO Unit := do
  let sys ← Lean.findSysroot
  Lean.initSearchPath sys
  let cwd ← IO.currentDir
  let localLib : System.FilePath := cwd / ".." / "lean" / ".lake" / "build" / "lib" / "lean"
  let mut sp := (← Lean.searchPathRef.get) ++ [localLib]
  let pkgs := #["mathlib","batteries","proofwidgets","Qq","aesop","importGraph","LeanSearchClient","plausible","Cli"]
  for nm in pkgs do
    let lib := cwd / ".." / "lean" / ".lake" / "packages" / nm / ".lake" / "build" / "lib" / "lean"
    if ← lib.pathExists then
      sp := sp ++ [lib]
  Lean.searchPathRef.set sp

def runIO (pref : String) : IO String := do
  setupSearchPath
  let env ← Lean.importModules #[{ module := `HeytingLean }] {}
  let coreCtx : Core.Context :=
    { fileName := "<cab_reflect>"
      fileMap := default
      currNamespace := `HeytingLean
      openDecls := [] }
  let coreState : Core.State := { env := env }
  let (s, _) ← (runReflect pref).toIO coreCtx coreState
  pure s

def main (args : List String) : IO UInt32 := do
  let pref := args.headD "HeytingLean"
  try
    let s ← runIO pref
    IO.println s
    return 0
  catch e =>
    IO.eprintln s!"cab_audit_reflect error: {e}"
    return 1
