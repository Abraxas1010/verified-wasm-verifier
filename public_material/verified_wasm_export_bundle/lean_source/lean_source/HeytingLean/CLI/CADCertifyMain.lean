import Lean
import Lean.Data.Json
import HeytingLean.Computational.RealConstraints.IR
import HeytingLean.Computational.RealConstraints.Cert
import HeytingLean.Computational.RealConstraints.Unsat
import HeytingLean.Computational.RealConstraints.UnsatInterval
import HeytingLean.Util.JCS
import HeytingLean.Util.SHA

/-!
# cad_certify

Runs `cad_solve`-style solving (dReal via Docker) and writes a stable certificate
that can be checked offline by `cad_verify`.

SAT certificates are *trusted only to the extent* that the witness check passes
under our approximate Float semantics.
-/

open Lean
open Lean.Json
open HeytingLean.Computational.RealConstraints

private def usage : String :=
  String.intercalate "\n"
    [ "cad_certify: produce a SAT-witness certificate for a real-constraints problem (JSON)"
    , ""
    , "Usage:"
    , "  cad_certify --in <problem.json> [--backend dreal|z3|yices] [--out <cert.json> | --outDir <dir>] [--eps <float>] [--unsatIntervalDepth <nat>]"
    , ""
    , "Defaults:"
    , "  --outDir out/cad"
    , "  --eps uses max(problem.precision, eps)"
    , "  --unsatIntervalDepth 10 (only used when solver reports unsat and no restricted checker matches)"
    , ""
    , "Backend:"
    , "  --backend dreal: docker run dreal/dreal4:latest python3 scripts/cad_dreal_solve.py"
    , "  --backend z3|yices: docker run heytinglean/smt-solvers:latest python3 scripts/cad_smt_solve.py"
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

private def parseNat? (s : String) : Option Nat :=
  s.trim.toNat?

private def repoRoot : IO System.FilePath := do
  let cwd ← IO.currentDir
  if cwd.fileName == some "lean" then
    return cwd.parent.getD cwd
  else
    return cwd

private def resolvePathRelativeToRepo (repo : System.FilePath) (path : String) : IO System.FilePath := do
  let p := System.FilePath.mk path
  if p.isAbsolute then
    return p
  return repo / p

private def resolvePathRelativeToCwd (path : String) : IO System.FilePath := do
  let cwd ← IO.currentDir
  let p := System.FilePath.mk path
  if p.isAbsolute then
    return p
  return cwd / p

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

private def witnessEnvOfModel (modelJson : Json) : Except String Json := do
  let obj ← modelJson.getObj?
  let mut fields : List (String × Json) := []
  for (k, v) in obj.toList do
    let o ← v.getObj?
    match o.get? "exact", o.get? "mid" with
    | some (.str s), _ => fields := fields.concat (k, Json.str s)
    | _, some midJ => fields := fields.concat (k, midJ)
    | _, _ => throw s!"model[{k}] missing field 'mid' (or 'exact')"
  pure (Json.mkObj fields)

def main (argv : List String) : IO Unit := do
  if argv.isEmpty || hasFlag argv "--help" then
    IO.eprintln usage
    IO.Process.exit 0

  let some inPathStr := parseArg argv "--in"
    | IO.eprintln usage; IO.Process.exit 0

  let backend := (parseArg argv "--backend").getD "dreal"

  let repo ← repoRoot
  let inAbs := (← resolvePathRelativeToCwd inPathStr)
  if !(← inAbs.pathExists) then
    IO.eprintln s!"E: input file not found: {inAbs}"
    IO.Process.exit 1

  let raw ← IO.FS.readFile inAbs
  let problemJson ←
    match Json.parse raw with
    | .ok j => pure j
    | .error e =>
        IO.eprintln s!"E: invalid JSON: {e}"
        IO.Process.exit 1

  let problem ←
    match Problem.ofJson problemJson with
    | .ok p => pure p
    | .error e =>
        IO.eprintln s!"E: invalid problem JSON: {e}"
        IO.Process.exit 1

  let jcs := HeytingLean.Util.JCS.canonicalString problemJson
  let sha ← HeytingLean.Util.sha256HexOfStringIO jcs

  let epsCli : Float := (parseArg argv "--eps").bind parseFloat? |>.getD 0.0
  let epsUsed : Float := max problem.precision epsCli

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

  let statusStr : Option String :=
    match solverJson.getObjVal? "status" with
    | .ok (.str s) => some s
    | _ => none

  let mut certified : Bool := false
  let mut checkMsg : Option String := none
  let mut witness : Json := Json.null
  let mut unsatCert : Json := Json.null
  let mut unsatIntervalCert : Json := Json.null

  match statusStr with
  | some "sat" =>
      match solverJson.getObjVal? "model" with
      | .ok (.obj m) =>
          match witnessEnvOfModel (.obj m) with
          | .error e =>
              certified := false
              checkMsg := some e
          | .ok envJ =>
              witness := Json.mkObj [("env", envJ), ("eps", Cert.jsonOfFloat epsUsed)]
              match Cert.envOfJsonObj envJ with
              | .error e =>
                  certified := false
                  checkMsg := some e
              | .ok env =>
                  match Cert.checkSatWitness problem env epsUsed with
                  | .ok ok =>
                      certified := ok
                      if !ok then checkMsg := some "witness check failed (Float, approximate)"
                  | .error e =>
                      certified := false
                      checkMsg := some e
      | .ok Json.null =>
          certified := false
          checkMsg := some "sat status but model = null"
      | _ =>
          certified := false
          checkMsg := some "sat status but missing/invalid model"
  | some "unsat" =>
      match Unsat.tryCertify problem with
      | none =>
          let maxDepth : Nat :=
            (parseArg argv "--unsatIntervalDepth").bind parseNat? |>.getD 10
          match UnsatInterval.tryCertify problemJson maxDepth with
          | .error e =>
              certified := false
              checkMsg := some s!"unsat interval cert generation failed: {e}"
          | .ok none =>
              certified := false
              checkMsg := some "unsat not certified (no local checker matched)"
          | .ok (some t) =>
              match UnsatInterval.verify problemJson t with
              | .error e =>
                  certified := false
                  checkMsg := some s!"unsat interval cert invalid: {e}"
              | .ok _ =>
                  certified := true
                  checkMsg := some s!"unsat certified by interval partition (depth={maxDepth})"
                  unsatIntervalCert :=
                    Json.mkObj
                      [ ("kind", Json.str "interval_tree")
                      , ("max_depth", Json.num (JsonNumber.fromNat maxDepth))
                      , ("tree", UnsatInterval.CertTree.toJson t)
                      ]
      | some r =>
          match Unsat.verifyReason problem r with
          | .ok _ =>
              certified := true
              checkMsg := some "unsat certified by local checker (restricted patterns)"
              unsatCert := Unsat.UnsatReason.toJson r
          | .error e =>
              certified := false
              checkMsg := some s!"unsat checker produced invalid certificate: {e}"
  | some "error" =>
      certified := false
      checkMsg := some "solver reported status=error"
  | some other =>
      certified := false
      checkMsg := some s!"unknown solver status: {other}"
  | none =>
      certified := false
      checkMsg := some "missing/invalid solver status"

  let certJson :=
    Json.mkObj <|
      [ ("version", Json.num (1 : JsonNumber))
      , ("problem_sha256", Json.str sha)
      , ("problem", problemJson)
      , ("problem_path", Json.str inAbs.toString)
      , ("backend", Json.str (match backend with | "dreal" => "dreal4" | "z3" => "z3" | "yices" => "yices" | other => other))
      , ("docker_image", Json.str (match backend with | "dreal" => "dreal/dreal4:latest" | "z3" | "yices" => "heytinglean/smt-solvers:latest" | other => other))
      , ("result", solverJson)
      , ("witness", witness)
      , ("unsat_cert", unsatCert)
      , ("unsat_interval_cert", unsatIntervalCert)
      , ("certified", Json.bool certified)
      ] ++ (match checkMsg with | some s => [("check_msg", Json.str s)] | none => [])

  let outPath ←
    match parseArg argv "--out" with
    | some p => resolvePathRelativeToRepo repo p
    | none =>
        let outDirStr := (parseArg argv "--outDir").getD "out/cad"
        let outDir ← resolvePathRelativeToRepo repo outDirStr
        pure (outDir / s!"cert_{sha}.json")

  IO.FS.createDirAll (outPath.parent.getD (System.FilePath.mk "."))
  IO.FS.writeFile outPath (toString certJson)

  let summary :=
    Json.mkObj
      ([ ("out", Json.str outPath.toString)
       , ("problem_sha256", Json.str sha)
       , ("status", match statusStr with | some s => Json.str s | none => Json.null)
       , ("certified", Json.bool certified)
       ])
  IO.println (toString summary)

  match statusStr with
  | some "sat" =>
      if certified then
        pure ()
      else
        IO.Process.exit 3
  | some "unsat" =>
      if certified then
        pure ()
      else
        IO.Process.exit 4
  | some "error" => IO.Process.exit 2
  | _ => IO.Process.exit 2
