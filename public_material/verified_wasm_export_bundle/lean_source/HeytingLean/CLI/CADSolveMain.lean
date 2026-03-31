import Lean
import Lean.Data.Json
import HeytingLean.Computational.RealConstraints.IR

/-!
# cad_solve

Executable bridge for quantifier-free real constraints (semi-algebraic / CAD-adjacent).

Current backend: dReal via Docker (`dreal/dreal4:latest`), using `scripts/cad_dreal_solve.py`.
-/

open Lean
open Lean.Json
open HeytingLean.Computational.RealConstraints

private def usage : String :=
  String.intercalate "\n"
    [ "cad_solve: dReal-backed solver for quantifier-free real constraints (JSON)"
    , ""
    , "Usage:"
    , "  cad_solve --in <problem.json> [--backend dreal|z3|yices] [--check] [--eps <float>]"
    , ""
    , "Notes:"
    , "  - Backend runs in Docker: dreal/dreal4:latest"
    , "  - SMT backends (z3/yices) run in Docker: heytinglean/smt-solvers:latest (build via scripts/build_smt_solvers_image.sh)"
    , "  - Problem format matches scripts/cad_dreal_solve.py"
    ]

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x :: y :: rest => if x == flag then some y else parseArg (y :: rest) flag
  | _ => none

private def hasFlag (xs : List String) (flag : String) : Bool :=
  xs.any (· == flag)

private def parseFloat? (s : String) : Option Float :=
  match Json.parse s.trim with
  | .ok (.num n) => some n.toFloat
  | _ => none

private def repoRoot : IO System.FilePath := do
  let cwd ← IO.currentDir
  if cwd.fileName == some "lean" then
    return cwd.parent.getD cwd
  else
    return cwd

private def midsFromModel (j : Json) : Except String Env := do
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

private def runDRealDocker (repo : System.FilePath) (inAbs : System.FilePath) : IO String := do
  let script := repo / "scripts" / "cad_dreal_solve.py"
  if !(← script.pathExists) then
    throw <| IO.userError s!"missing solver script: {script}"

  let inDir := inAbs.parent.getD (System.FilePath.mk ".")
  let inFile := inAbs.fileName.getD inAbs.toString
  let inContainer := s!"/input/{inFile}"

  let args : Array String :=
    #[
      "run", "--rm",
      "-v", s!"{repo.toString}:/repo",
      "-v", s!"{inDir.toString}:/input",
      "-w", "/repo",
      "dreal/dreal4:latest",
      "python3", "scripts/cad_dreal_solve.py",
      "--in", inContainer
    ]

  let out ← IO.Process.output { cmd := "docker", args := args }
  if out.exitCode != 0 then
    throw <| IO.userError s!"dreal docker failed (exit={out.exitCode}): {out.stderr}"
  pure out.stdout

private def runSMTDocker (repo : System.FilePath) (inAbs : System.FilePath) (solver : String) : IO String := do
  let script := repo / "scripts" / "cad_smt_solve.py"
  if !(← script.pathExists) then
    throw <| IO.userError s!"missing solver script: {script}"

  let image := "heytinglean/smt-solvers:latest"
  let imgCheck ← IO.Process.output { cmd := "docker", args := #["image", "inspect", image] }
  if imgCheck.exitCode != 0 then
    throw <| IO.userError s!"missing docker image '{image}' (build via scripts/build_smt_solvers_image.sh)"

  let inDir := inAbs.parent.getD (System.FilePath.mk ".")
  let inFile := inAbs.fileName.getD inAbs.toString
  let inContainer := s!"/input/{inFile}"

  let args : Array String :=
    #[
      "run", "--rm",
      "-v", s!"{repo.toString}:/repo",
      "-v", s!"{inDir.toString}:/input",
      "-w", "/repo",
      image,
      "python3", "scripts/cad_smt_solve.py",
      "--solver", solver,
      "--in", inContainer
    ]

  let out ← IO.Process.output { cmd := "docker", args := args }
  if out.exitCode != 0 then
    throw <| IO.userError s!"smt docker failed (exit={out.exitCode}): {out.stderr}"
  pure out.stdout

def main (argv : List String) : IO Unit := do
  if argv.isEmpty || hasFlag argv "--help" then
    IO.eprintln usage
    IO.Process.exit 0

  let some inPathStr := parseArg argv "--in"
    | IO.eprintln usage; IO.Process.exit 1

  let check := hasFlag argv "--check"
  let eps : Float :=
    match (parseArg argv "--eps").bind parseFloat? with
    | some x => x
    | none => 1e-6

  let backend := (parseArg argv "--backend").getD "dreal"

  let repo ← repoRoot
  let cwd ← IO.currentDir
  let inPath := System.FilePath.mk inPathStr
  let inAbs := if inPath.isAbsolute then inPath else cwd / inPath

  if !(← inAbs.pathExists) then
    IO.eprintln s!"E: input file not found: {inAbs}"
    IO.Process.exit 1

  let problemTxt ← IO.FS.readFile inAbs
  let problem ←
    match Problem.parseString problemTxt with
    | .ok p => pure p
    | .error e =>
        IO.eprintln s!"E: invalid problem JSON: {e}"
        IO.Process.exit 1

  let solverOut ←
    try
      match backend with
      | "dreal" => runDRealDocker repo inAbs
      | "z3" => runSMTDocker repo inAbs "z3"
      | "yices" => runSMTDocker repo inAbs "yices"
      | other => throw <| IO.userError s!"unknown backend '{other}'"
    catch e =>
      IO.eprintln s!"E: solver failure: {e}"
      IO.Process.exit 2

  let solverJson ←
    match Json.parse solverOut with
    | .ok j => pure j
    | .error e =>
        IO.eprintln s!"E: solver returned invalid JSON: {e}"
        IO.Process.exit 2

  let mut checked : Option Bool := none
  let mut checkMsg : Option String := none

  let statusStr : Option String :=
    match solverJson.getObjVal? "status" with
    | .ok (.str s) => some s
    | _ => none

  if check then
    match statusStr with
    | some "sat" =>
        match solverJson.getObjVal? "model" with
        | .ok (.obj m) =>
            match midsFromModel (.obj m) with
            | .error e =>
                checked := some false
                checkMsg := some e
            | .ok env =>
                let eps' := max eps problem.precision
                match Formula.eval env eps' problem.formula with
                | .ok ok =>
                    checked := some ok
                    if !ok then checkMsg := some "witness check failed (Float, approximate)"
                | .error e =>
                    checked := some false
                    checkMsg := some e
        | .ok Json.null =>
            checked := some false
            checkMsg := some "sat status but model = null"
        | _ =>
            checked := some false
            checkMsg := some "sat status but missing/invalid model"
    | some _ =>
        checked := some true
        checkMsg := some "no witness to check (status != sat)"
    | none =>
        checked := some false
        checkMsg := some "missing/invalid solver status"

  let baseFields : List (String × Json) :=
    [ ("problem", Json.str inAbs.toString)
    , ("result", solverJson)
    ]
  let fields :=
    match checked with
    | none => baseFields
    | some b =>
        let msgField := match checkMsg with | some s => [("check_msg", Json.str s)] | none => []
        baseFields ++ [("checked", Json.bool b)] ++ msgField

  IO.println <| toString <| Json.mkObj fields

  -- Exit codes: preserve JSON output, but make failures machine-detectable.
  match statusStr with
  | some "error" => IO.Process.exit 2
  | _ =>
      match (check, checked) with
      | (true, some false) => IO.Process.exit 3
      | _ => pure ()
