import Lean
import Lean.Data.Json
import HeytingLean.Computational.RealConstraints.IR
import HeytingLean.Computational.RealConstraints.Cert
import HeytingLean.Computational.RealConstraints.RatCheck
import HeytingLean.Computational.RealConstraints.Unsat
import HeytingLean.Computational.RealConstraints.UnsatInterval
import HeytingLean.Util.JCS
import HeytingLean.Util.SHA

/-!
# cad_verify

Offline verifier for `cad_certify` certificates.

This checks:
- the stored `problem_sha256` matches the problem JSON (JCS + SHA-256),
- the SAT witness (if present) satisfies variable bounds and the formula,
  under approximate Float semantics.
-/

open Lean
open Lean.Json
open HeytingLean.Computational.RealConstraints

private def usage : String :=
  String.intercalate "\n"
    [ "cad_verify: verify a real-constraints SAT-witness certificate (JSON)"
    , ""
    , "Usage:"
    , "  cad_verify --cert <cert.json> [--exact]"
    , ""
    , "Modes:"
    , "  (default) Float+eps approximate witness checking"
    , "  --exact   exact rational checking (requires JSON-parsable rationals)"
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

private def resolvePathRelativeToRepo (repo : System.FilePath) (path : String) : IO System.FilePath := do
  let p := System.FilePath.mk path
  if p.isAbsolute then
    return p
  return repo / p

def main (argv : List String) : IO Unit := do
  if argv.isEmpty || hasFlag argv "--help" then
    IO.eprintln usage
    IO.Process.exit 0

  let some certPathStr := parseArg argv "--cert"
    | IO.eprintln usage; IO.Process.exit 0

  let repo ← repoRoot
  let certPath := (← resolvePathRelativeToRepo repo certPathStr)
  if !(← certPath.pathExists) then
    IO.eprintln s!"E: certificate file not found: {certPath}"
    IO.Process.exit 1

  let raw ← IO.FS.readFile certPath
  let certJson ←
    match Json.parse raw with
    | .ok j => pure j
    | .error e =>
        IO.eprintln s!"E: invalid certificate JSON: {e}"
        IO.Process.exit 1

  let certObj ←
    match certJson.getObj? with
    | .ok o => pure o
    | .error _ =>
        IO.eprintln "E: certificate must be a JSON object"
        IO.Process.exit 1

  let problemJson ←
    match certObj.get? "problem" with
    | some j => pure j
    | none =>
        IO.eprintln "E: certificate missing field 'problem'"
        IO.Process.exit 1

  let shaStored ←
    match certObj.get? "problem_sha256" with
    | some (.str s) => pure s
    | _ =>
        IO.eprintln "E: certificate missing/invalid field 'problem_sha256'"
        IO.Process.exit 1

  let shaComputed ←
    HeytingLean.Util.sha256HexOfStringIO (HeytingLean.Util.JCS.canonicalString problemJson)

  let hashOk := (shaStored == shaComputed)

  let problem ←
    match Problem.ofJson problemJson with
    | .ok p => pure p
    | .error e =>
        IO.eprintln s!"E: invalid embedded problem JSON: {e}"
        IO.Process.exit 1

  let witnessJ := certObj.get? "witness" |>.getD Json.null
  let unsatCertJ := certObj.get? "unsat_cert" |>.getD Json.null
  let unsatIntervalCertJ := certObj.get? "unsat_interval_cert" |>.getD Json.null
  let exact := hasFlag argv "--exact"
  if witnessJ == Json.null then
    if unsatIntervalCertJ != Json.null then
      let (verified, msg) : Bool × String :=
        match unsatIntervalCertJ.getObj? with
        | .error _ => (false, "unsat_interval_cert must be an object or null")
        | .ok o =>
            match o.get? "tree" with
            | none => (false, "unsat_interval_cert missing field 'tree'")
            | some treeJ =>
                match UnsatInterval.CertTree.ofJson treeJ with
                | .error e => (false, s!"invalid interval tree: {e}")
                | .ok t =>
                    match UnsatInterval.verify problemJson t with
                    | .ok _ => (true, "ok")
                    | .error e => (false, e)
      let out :=
        Json.mkObj
          [ ("cert", Json.str certPath.toString)
          , ("problem_sha256_ok", Json.bool hashOk)
          , ("mode", Json.str "unsat_interval")
          , ("verified", Json.bool verified)
          , ("msg", Json.str msg)
          ]
      IO.println (toString out)
      if !hashOk then
        IO.Process.exit 2
      else if verified then
        IO.Process.exit 0
      else
        IO.Process.exit 3
    else if unsatCertJ != Json.null then
      let (verified, msg) : Bool × String :=
        match Unsat.UnsatReason.ofJson unsatCertJ with
        | .error e => (false, s!"invalid unsat_cert: {e}")
        | .ok r =>
            match Unsat.verifyReason problem r with
            | .ok _ => (true, "ok")
            | .error e => (false, e)
      let out :=
        Json.mkObj
          [ ("cert", Json.str certPath.toString)
          , ("problem_sha256_ok", Json.bool hashOk)
          , ("mode", Json.str "unsat_restricted")
          , ("verified", Json.bool verified)
          , ("msg", Json.str msg)
          ]
      IO.println (toString out)
      if !hashOk then
        IO.Process.exit 2
      else if verified then
        IO.Process.exit 0
      else
        IO.Process.exit 3
    else
      let out :=
        Json.mkObj
          [ ("cert", Json.str certPath.toString)
          , ("problem_sha256_ok", Json.bool hashOk)
          , ("mode", Json.str "no_witness")
          , ("verified", Json.bool false)
          , ("msg", Json.str "no witness present (UNSAT/unknown not certified)")
          ]
      IO.println (toString out)
      IO.Process.exit 4

  let wObj ←
    match witnessJ.getObj? with
    | .ok o => pure o
    | .error _ =>
        IO.eprintln "E: witness must be an object or null"
        IO.Process.exit 1

  let envJ ←
    match wObj.get? "env" with
    | some j => pure j
    | none =>
        IO.eprintln "E: witness missing field 'env'"
        IO.Process.exit 1

  if exact then
    let envRat ←
      match RatCheck.envOfJsonObj envJ with
      | .ok e => pure e
      | .error e =>
          IO.eprintln s!"E: invalid witness env (exact mode): {e}"
          IO.Process.exit 1
    let (verified, msg) : Bool × String :=
      match RatCheck.checkSatWitnessExact problemJson envRat with
      | .ok true => (true, "ok")
      | .ok false => (false, "formula check returned false")
      | .error e => (false, e)
    let out :=
      Json.mkObj
        [ ("cert", Json.str certPath.toString)
        , ("problem_sha256_ok", Json.bool hashOk)
        , ("mode", Json.str "exact")
        , ("verified", Json.bool verified)
        , ("msg", Json.str msg)
        ]
    IO.println (toString out)
    if !hashOk then
      IO.Process.exit 2
    else if verified then
      pure ()
    else
      IO.Process.exit 3
  else
    let epsUsed : Float :=
      match wObj.get? "eps" with
      | some (.num n) => n.toFloat
      | some (.str s) => (parseFloat? s).getD problem.precision
      | _ => problem.precision

    let env ←
      match Cert.envOfJsonObj envJ with
      | .ok e => pure e
      | .error e =>
          IO.eprintln s!"E: invalid witness env: {e}"
          IO.Process.exit 1
    let (verified, msg) : Bool × String :=
      match Cert.checkSatWitness problem env epsUsed with
      | .ok true => (true, "ok")
      | .ok false => (false, "formula check returned false")
      | .error e => (false, e)

    let out :=
      Json.mkObj
        [ ("cert", Json.str certPath.toString)
        , ("problem_sha256_ok", Json.bool hashOk)
        , ("mode", Json.str "float")
        , ("verified", Json.bool verified)
        , ("eps", Cert.jsonOfFloat epsUsed)
        , ("msg", Json.str msg)
        ]
    IO.println (toString out)

    if !hashOk then
      IO.Process.exit 2
    else if verified then
      pure ()
    else
      IO.Process.exit 3
