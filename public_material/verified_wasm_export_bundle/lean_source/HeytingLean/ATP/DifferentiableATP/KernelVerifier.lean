import Lean.Data.Json
import HeytingLean.ATP.DifferentiableATP.TacticDecoder

/-!
# ATP.DifferentiableATP.KernelVerifier

Attempts to replay decoded tactics by invoking `lake env lean` on generated wrappers.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open Lean

structure Attempt where
  tactic : String
  source : String
  wrapperPath : String
  rc : UInt32
  ok : Bool
  stdout : String
  stderr : String
  deriving Repr

structure VerificationResult where
  ok : Bool
  verifiedTactic : Option String
  attempts : List Attempt
  reason : String
  deriving Repr

private def sanitizeGoalExpr (goal : String) : String :=
  let g := goal.trim
  if g.startsWith "⊢" then
    (g.drop 1).trim
  else
    g

private def wrapperImports : List String :=
  [ "import Mathlib.Tactic.Basic"
  , "import Mathlib.Tactic.Ring"
  , "import Mathlib.Tactic.Linarith"
  , "import Mathlib.Tactic.NormNum"
  , "import Mathlib.Tactic.Tauto"
  , "import Mathlib.Tactic.Cases"
  , "import Aesop"
  , "import Lean.Elab.Tactic.Omega"
  ]

private def wrapperText (goalExpr tactic : String) : String :=
  String.intercalate "\n"
    (wrapperImports ++
      [ "set_option autoImplicit false"
      , s!"example : {goalExpr} := by"
      , s!"  {tactic}"
      , ""
      ])

private def ensureTmpDir : IO System.FilePath := do
  let dir := System.FilePath.mk ".tmp" / "differentiable_atp"
  IO.FS.createDirAll dir
  pure dir

private def writeWrapper (goalExpr tactic : String) (idx : Nat) : IO System.FilePath := do
  let dir ← ensureTmpDir
  let tag : UInt64 := hash (goalExpr ++ "|" ++ tactic ++ "|" ++ toString idx)
  let path := dir / s!"wrapper_{idx}_{tag}.lean"
  IO.FS.writeFile path (wrapperText goalExpr tactic)
  pure path

private def runWrapper (path : System.FilePath) : IO IO.Process.Output := do
  let out ←
    IO.Process.output
      { cmd := "lake"
        args := #["env", "lean", path.toString]
        cwd := some (System.FilePath.mk ".") }
  let stderrLines := (out.stderr.splitOn "\n").map String.trim |>.filter (fun s => !s.isEmpty)
  let warningOnly :=
    out.exitCode != 0 &&
    !stderrLines.isEmpty &&
    stderrLines.all (fun line =>
      line.startsWith "warning:" &&
      (line.splitOn "repository").length > 1 &&
      (line.splitOn "has local changes").length > 1) &&
    (out.stderr.splitOn "error:").length == 1 &&
    (out.stdout.splitOn "error:").length == 1 &&
    (out.stderr.splitOn "unsolved goals").length == 1 &&
    (out.stdout.splitOn "unsolved goals").length == 1 &&
    (out.stderr.splitOn "failed to").length == 1 &&
    (out.stdout.splitOn "failed to").length == 1
  if warningOnly then
    let lpOut ←
      IO.Process.output
        { cmd := "lake"
          args := #["env", "printenv", "LEAN_PATH"]
          cwd := some (System.FilePath.mk ".") }
    let leanPath := lpOut.stdout.trim
    if lpOut.exitCode == 0 && !leanPath.isEmpty then
      IO.Process.output
        { cmd := "env"
          args := #[s!"LEAN_PATH={leanPath}", "lean", path.toString]
          cwd := some (System.FilePath.mk ".") }
    else
      pure out
  else
    pure out

private def decodeAttempt (tactic source : String) (path : System.FilePath) (out : IO.Process.Output) : Attempt :=
  {
    tactic := tactic
    source := source
    wrapperPath := path.toString
    rc := out.exitCode
    ok := out.exitCode == 0
    stdout := out.stdout
    stderr := out.stderr
  }

private def builtInFallbackTactics : List (String × String) :=
  [
    ("exact True.intro", "fallback"),
    ("trivial", "fallback"),
    ("simp", "fallback"),
    ("aesop", "fallback"),
    ("rfl", "fallback"),
    ("decide", "fallback"),
    ("ring", "fallback"),
    ("omega", "fallback"),
    ("norm_num", "fallback"),
    ("linarith", "fallback"),
    ("tauto", "fallback"),
    ("contradiction", "fallback")
  ]

private def confidenceSorted (decoded : List DecodedCandidate) : List DecodedCandidate :=
  decoded.toArray.qsort (fun a b => a.confidence > b.confidence) |>.toList

/-- Standard solver suffixes used for tactic composition. -/
private def solverSuffixes : List String :=
  ["omega", "ring", "simp", "norm_num", "linarith", "decide"]

/-- Check if a tactic is a structural prefix suitable for composition. -/
private def isStructuralPrefix (tactic : String) : Bool :=
  tactic.startsWith "intro" || tactic.startsWith "constructor" ||
  tactic.startsWith "cases" || tactic.startsWith "apply" ||
  tactic.startsWith "simp_all" || tactic.startsWith "simp only"

/-- Generate tactic compositions: pair decoded structural tactics with solver suffixes. -/
private def composeTactics (decoded : List DecodedCandidate) (budget : Nat := 6) : List (String × String) :=
  let structural := decoded.filter (fun d => isStructuralPrefix d.tactic)
  let compositions := structural.foldl
    (fun acc d =>
      solverSuffixes.foldl
        (fun acc2 suffix =>
          if d.tactic == suffix then acc2  -- skip self-composition
          else
            let composed := s!"{d.tactic}; {suffix}"
            let source := s!"composition::{d.source}+{suffix}"
            acc2 ++ [(composed, source)])
        acc)
    []
  compositions.take (max 1 budget)

private def candidateTactics (decoded : List DecodedCandidate) (expandFallbacks : Bool := false) : List (String × String) :=
  let sorted := confidenceSorted decoded
  let fromDecoded := sorted.map (fun d => (d.tactic, d.source))
  let compositions := if expandFallbacks then composeTactics sorted else []
  (fromDecoded ++ compositions ++ builtInFallbackTactics).foldl
    (fun acc row => if acc.any (fun x => x.1 = row.1) then acc else acc ++ [row])
    []

def verify (goal : String) (decoded : List DecodedCandidate) (maxAttempts : Nat := 4) (expandFallbacks : Bool := false) : IO VerificationResult := do
  let goalExpr := sanitizeGoalExpr goal
  if goalExpr.isEmpty then
    return { ok := false, verifiedTactic := none, attempts := [], reason := "empty_goal_expression" }
  let tactics := (candidateTactics decoded expandFallbacks).take (max 1 maxAttempts)
  let rec go (rest : List (String × String)) (idx : Nat) (acc : List Attempt) : IO VerificationResult := do
    match rest with
    | [] =>
        return {
          ok := false
          verifiedTactic := none
          attempts := acc.reverse
          reason := "no_candidate_verified"
        }
    | (tactic, source) :: tail =>
        let wrapper ← writeWrapper goalExpr tactic idx
        let out ← runWrapper wrapper
        let attempt := decodeAttempt tactic source wrapper out
        if attempt.ok then
          return {
            ok := true
            verifiedTactic := some tactic
            attempts := (attempt :: acc).reverse
            reason := "kernel_verified"
          }
        else
          go tail (idx + 1) (attempt :: acc)
  go tactics 1 []

def toJson (r : VerificationResult) : Json :=
  let attemptsJson :=
    Json.arr <| r.attempts.toArray.map (fun a =>
      Json.mkObj
        [ ("tactic", Json.str a.tactic)
        , ("source", Json.str a.source)
        , ("wrapper_path", Json.str a.wrapperPath)
        , ("rc", Json.num a.rc.toNat)
        , ("ok", Json.bool a.ok)
        , ("stderr", Json.str a.stderr)
        ])
  Json.mkObj
    [ ("ok", Json.bool r.ok)
    , ("verified_tactic", match r.verifiedTactic with | some t => Json.str t | none => Json.null)
    , ("reason", Json.str r.reason)
    , ("attempts", attemptsJson)
    ]

end DifferentiableATP
end ATP
end HeytingLean
