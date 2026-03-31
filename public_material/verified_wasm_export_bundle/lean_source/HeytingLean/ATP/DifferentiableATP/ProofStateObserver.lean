import HeytingLean.ATP.DifferentiableATP.KernelVerifier

/-!
# ATP.DifferentiableATP.ProofStateObserver

Observe remaining subgoals after applying a tactic to a goal by compiling
generated Lean wrappers.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open Lean

structure ProofStateResult where
  ok : Bool
  remainingGoals : List String
  originalGoal : String
  appliedTactic : String
  stderr : String
  timedOut : Bool := false
  deriving Repr

private def sanitizeGoalExpr (goal : String) : String :=
  let g := goal.trim
  if g.startsWith "⊢" then
    (g.drop 1).trim
  else
    g

private def indentBlock (txt : String) : String :=
  String.intercalate "\n" ((txt.splitOn "\n").map (fun line => s!"  {line}"))

private def indentNestedBlock (txt : String) : String :=
  indentBlock (indentBlock txt)

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

private def wrapperBuildTargets : Array String :=
  #[ "Mathlib.Tactic.Basic"
   , "Mathlib.Tactic.Ring"
   , "Mathlib.Tactic.Linarith"
   , "Mathlib.Tactic.NormNum"
   , "Mathlib.Tactic.Tauto"
   , "Mathlib.Tactic.Cases"
   , "Aesop"
   ]

private def wrapperWithObserverText (goalExpr tactic : String) : String :=
  String.intercalate "\n"
    (wrapperImports ++
      [ "open Lean Elab Tactic Meta"
      , "set_option autoImplicit false"
      , ""
      , "elab \"emit_remaining\" : tactic => do"
      , "  let goals ← Lean.Elab.Tactic.getUnsolvedGoals"
      , "  if goals.isEmpty then"
      , "    Lean.logInfo m!\"[PROVED]\""
      , "  else"
      , "    for g in goals do"
      , "      let ty ← Lean.Meta.getMVarType g"
      , "      let fmt ← Lean.Meta.ppExpr ty"
      , "      Lean.logInfo m!\"[GOAL]{fmt}[/GOAL]\""
      , "      Lean.Elab.admitGoal g"
      , ""
      , s!"example : {goalExpr} := by"
      , indentBlock tactic
      , "  emit_remaining"
      , ""
      ])

private def wrapperFallbackText (goalExpr tactic : String) : String :=
  String.intercalate "\n"
    (wrapperImports ++
      [ "set_option autoImplicit false"
      , s!"example : {goalExpr} := by"
      , indentBlock tactic
      , ""
      ])

private def wrapperProofScriptText (goalExpr : String) (tactics : List String) : String :=
  String.intercalate "\n"
    ((wrapperImports ++
      [ "set_option autoImplicit false"
      , s!"example : {goalExpr} := by"
      ])
      ++ tactics.map indentBlock
      ++ [""])

private def batchAttemptText (idx : Nat) (goalExpr tactic : String) : List String :=
  [ s!"section attempt_{idx}"
  , s!"example : {goalExpr} := by"
  , s!"  run_batched_attempt {idx} =>"
  , indentNestedBlock tactic
  , s!"end attempt_{idx}"
  , ""
  ]

private def wrapperBatchText (pairs : List (String × String)) : String :=
  let prelude :=
    wrapperImports ++
      [ "open Lean Elab Tactic Meta"
      , "set_option autoImplicit false"
      , ""
      , "elab \"run_batched_attempt \" idx:num \" => \" body:tacticSeq : tactic => do"
      , "  let i := idx.getNat"
      , "  Lean.logInfo m!\"[ATTEMPT_BEGIN]{i}[/ATTEMPT_BEGIN]\""
      , "  let emit : TacticM Unit := do"
      , "    let goals ← Lean.Elab.Tactic.getUnsolvedGoals"
      , "    if goals.isEmpty then"
      , "      Lean.logInfo m!\"[PROVED]\""
      , "    else"
      , "      for g in goals do"
      , "        let ty ← Lean.Meta.getMVarType g"
      , "        let fmt ← Lean.Meta.ppExpr ty"
      , "        Lean.logInfo m!\"[GOAL]{fmt}[/GOAL]\""
      , "        Lean.Elab.admitGoal g"
      , "  try"
      , "    Lean.Elab.Tactic.evalTactic body"
      , "    emit"
      , "  catch _ =>"
      , "    Lean.logInfo m!\"[ATTEMPT_ERROR]\""
      , "    emit"
      , "  Lean.logInfo m!\"[ATTEMPT_END]{i}[/ATTEMPT_END]\""
      , ""
      ]
  let indexedPairs := List.zip (List.range pairs.length) pairs
  let attempts :=
    indexedPairs.foldr (fun entry acc =>
      let idx := entry.1
      let goalExpr := sanitizeGoalExpr entry.2.1
      let tactic := entry.2.2
      batchAttemptText idx goalExpr tactic ++ acc) []
  String.intercalate "\n" (prelude ++ attempts)

private def ensureTmpDir : IO System.FilePath := do
  let dir := System.FilePath.mk ".tmp" / "differentiable_atp"
  IO.FS.createDirAll dir
  pure dir

private def ensureWrapperImportsBuilt : IO Unit := do
  let dir ← ensureTmpDir
  let stamp := dir / "observer_imports_ready_v1.txt"
  let stampKey := String.intercalate "|" wrapperImports
  let alreadyReady ← do
    if (← System.FilePath.pathExists stamp) then
      let recorded ← IO.FS.readFile stamp
      pure (recorded.trim == stampKey)
    else
      pure false
  if alreadyReady then
    pure ()
  else
    let out ←
      IO.Process.output
        { cmd := "lake"
          args := #["build"] ++ wrapperBuildTargets
          cwd := some (System.FilePath.mk ".") }
    if out.exitCode == 0 then
      IO.FS.writeFile stamp stampKey
    else
      let stdout := out.stdout.trim
      let stderr := out.stderr.trim
      let logs :=
        if stdout.isEmpty then stderr
        else if stderr.isEmpty then stdout
        else stdout ++ "\n" ++ stderr
      throw <| IO.userError s!"observer_import_prelude_build_failed: {logs}"

private def writeWrapper (goalExpr tactic : String) (tag : String) : IO System.FilePath := do
  let dir ← ensureTmpDir
  let digest : UInt64 := hash (goalExpr ++ "|" ++ tactic ++ "|" ++ tag)
  let path := dir / s!"observer_{tag}_{digest}.lean"
  let body :=
    if tag = "primary" then
      wrapperWithObserverText goalExpr tactic
    else
      wrapperFallbackText goalExpr tactic
  IO.FS.writeFile path body
  pure path

private def writeProofScriptWrapper (goalExpr : String) (tactics : List String) : IO System.FilePath := do
  let dir ← ensureTmpDir
  let scriptKey := String.intercalate " ; " tactics
  let digest : UInt64 := hash (goalExpr ++ "|" ++ scriptKey ++ "|proof_recheck")
  let path := dir / s!"observer_recheck_{digest}.lean"
  IO.FS.writeFile path (wrapperProofScriptText goalExpr tactics)
  pure path

private def writeBatchWrapper (pairs : List (String × String)) : IO System.FilePath := do
  let dir ← ensureTmpDir
  let key :=
    String.intercalate "||"
      (pairs.map (fun entry =>
        let goalExpr := sanitizeGoalExpr entry.1
        s!"{goalExpr}=>{entry.2}"))
  let digest : UInt64 := hash (key ++ "|batch")
  let path := dir / s!"observer_batch_{pairs.length}_{digest}.lean"
  IO.FS.writeFile path (wrapperBatchText pairs)
  pure path

private def runWrapperWithTimeout (path : System.FilePath) (timeoutSeconds : Nat) : IO IO.Process.Output := do
  let t := s!"{max 1 timeoutSeconds}s"
  let out0 ←
    IO.Process.output
      { cmd := "timeout"
        args := #["--signal=KILL", t, "lake", "env", "lean", path.toString]
        cwd := some (System.FilePath.mk ".") }
  let out ←
    if out0.exitCode == 127 then
      IO.Process.output
        { cmd := "lake"
          args := #["env", "lean", path.toString]
          cwd := some (System.FilePath.mk ".") }
    else
      pure out0
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
      let directOut ←
        IO.Process.output
          { cmd := "timeout"
            args := #["--signal=KILL", t, "env", s!"LEAN_PATH={leanPath}", "lean", path.toString]
            cwd := some (System.FilePath.mk ".") }
      if directOut.exitCode == 127 then
        IO.Process.output
          { cmd := "env"
            args := #[s!"LEAN_PATH={leanPath}", "lean", path.toString]
            cwd := some (System.FilePath.mk ".") }
      else
        pure directOut
    else
      pure out
  else
    pure out

private def hasMarker (txt marker : String) : Bool :=
  (txt.splitOn marker).length > 1

private def extractGoalMarkers (txt : String) : List String :=
  ((txt.splitOn "[GOAL]").drop 1).filterMap (fun chunk =>
    match chunk.splitOn "[/GOAL]" with
    | [] => none
    | goal :: _ =>
        let g := goal.trim
        if g.isEmpty then none else some g)

private def extractGoalLines (txt : String) : List String :=
  (txt.splitOn "\n").filterMap (fun line =>
    let t := line.trim
    if t.startsWith "⊢" then some t else none)

private def attemptBeginMarker (idx : Nat) : String :=
  s!"[ATTEMPT_BEGIN]{idx}[/ATTEMPT_BEGIN]"

private def attemptEndMarker (idx : Nat) : String :=
  s!"[ATTEMPT_END]{idx}[/ATTEMPT_END]"

private def extractBetween (txt beginMarker endMarker : String) : Option String :=
  match txt.splitOn beginMarker with
  | [] => none
  | _ :: tail =>
      match tail with
      | [] => none
      | after :: _ =>
          match after.splitOn endMarker with
          | [] => none
          | chunk :: _ => some chunk

private def combineLogs (out : IO.Process.Output) : String :=
  let a := out.stdout.trim
  let b := out.stderr.trim
  if a.isEmpty then b
  else if b.isEmpty then a
  else a ++ "\n" ++ b

private def unresolvedSentinel : String :=
  "⊢ _observer_unresolved"

private def isTimeoutExitCode (exitCode : UInt32) : Bool :=
  exitCode == 124 || exitCode == 137

private def nonEmptyGoals (goals : List String) : List String :=
  let gs := goals.eraseDups.filter (fun g => !g.trim.isEmpty)
  if gs.isEmpty then [unresolvedSentinel] else gs

def observe (goal tactic : String) (timeoutSeconds : Nat := 20) : IO ProofStateResult := do
  ensureWrapperImportsBuilt
  let goalExpr := sanitizeGoalExpr goal
  if goalExpr.isEmpty then
    return {
      ok := false
      remainingGoals := []
      originalGoal := goal
      appliedTactic := tactic
      stderr := "empty_goal_expression"
      timedOut := false
    }

  let primaryWrapper ← writeWrapper goalExpr tactic "primary"
  let primaryOut ← runWrapperWithTimeout primaryWrapper timeoutSeconds
  let primaryTimedOut := isTimeoutExitCode primaryOut.exitCode
  let primaryLogs := combineLogs primaryOut
  let primaryGoals := (extractGoalMarkers primaryLogs).eraseDups
  let primaryProved := hasMarker primaryLogs "[PROVED]"
  if primaryOut.exitCode == 0 then
    let remaining := if primaryProved then [] else nonEmptyGoals primaryGoals
    return {
      ok := true
      remainingGoals := remaining
      originalGoal := goal
      appliedTactic := tactic
      stderr := primaryLogs
      timedOut := false
    }

  let fallbackWrapper ← writeWrapper goalExpr tactic "fallback"
  let fallbackOut ← runWrapperWithTimeout fallbackWrapper timeoutSeconds
  let fallbackTimedOut := isTimeoutExitCode fallbackOut.exitCode
  let fallbackLogs := combineLogs fallbackOut
  let fallbackGoals := (extractGoalLines fallbackLogs).eraseDups
  let fallbackUnsolved := hasMarker fallbackLogs "unsolved goals"
  let treatAsPartial := fallbackUnsolved || !fallbackGoals.isEmpty
  if fallbackOut.exitCode == 0 || treatAsPartial then
    let remaining :=
      if fallbackOut.exitCode == 0 && !fallbackUnsolved && fallbackGoals.isEmpty then
        []
      else
        nonEmptyGoals fallbackGoals
    return {
      ok := true
      remainingGoals := remaining
      originalGoal := goal
      appliedTactic := tactic
      stderr := fallbackLogs
      timedOut := primaryTimedOut || fallbackTimedOut
    }

  pure
    { ok := false
      remainingGoals := []
      originalGoal := goal
      appliedTactic := tactic
      stderr := fallbackLogs
      timedOut := primaryTimedOut || fallbackTimedOut }

private def chunkList (rows : List α) (chunkSize : Nat) : List (List α) :=
  let size := max 1 chunkSize
  Id.run do
    let mut remaining := rows
    let mut acc : List (List α) := []
    while !remaining.isEmpty do
      let chunk := remaining.take size
      remaining := remaining.drop size
      acc := chunk :: acc
    return acc.reverse

private def observeBatchSerial
    (pairs : List (String × String))
    (timeoutSeconds : Nat := 60) : IO (List ProofStateResult) := do
  if pairs.isEmpty then
    return []
  ensureWrapperImportsBuilt
  let wrapper ← writeBatchWrapper pairs
  let out ← runWrapperWithTimeout wrapper timeoutSeconds
  let logs := combineLogs out
  let timedOut := isTimeoutExitCode out.exitCode
  let mut results : List ProofStateResult := []
  let indexedPairs := List.zip (List.range pairs.length) pairs
  for entry in indexedPairs do
    let idx := entry.1
    let goal := entry.2.1
    let tactic := entry.2.2
    let goalExpr := sanitizeGoalExpr goal
    if goalExpr.isEmpty then
      results := results ++
        [{ ok := false
           remainingGoals := []
           originalGoal := goal
           appliedTactic := tactic
           stderr := "empty_goal_expression"
           timedOut := false }]
    else
      let begin := attemptBeginMarker idx
      let endm := attemptEndMarker idx
      match extractBetween logs begin endm with
      | some chunk =>
          let proved := hasMarker chunk "[PROVED]"
          let goals := (extractGoalMarkers chunk).eraseDups
          let remaining := if proved then [] else nonEmptyGoals goals
          results := results ++
            [{ ok := true
               remainingGoals := remaining
               originalGoal := goal
               appliedTactic := tactic
               stderr := chunk
               timedOut := timedOut }]
      | none =>
          if timedOut then
            results := results ++
              [{ ok := false
                 remainingGoals := []
                 originalGoal := goal
                 appliedTactic := tactic
                 stderr := logs
                 timedOut := true }]
          else
            let single ← observe goal tactic timeoutSeconds
            results := results ++ [single]
  return results

def observeBatch
    (pairs : List (String × String))
    (timeoutSeconds : Nat := 60)
    (parallelWorkers : Nat := 1) : IO (List ProofStateResult) := do
  if pairs.isEmpty then
    return []
  let workers := max 1 parallelWorkers
  if workers = 1 || pairs.length <= 1 then
    observeBatchSerial pairs timeoutSeconds
  else
    let chunkSize := max 1 ((pairs.length + workers - 1) / workers)
    let chunks := chunkList pairs chunkSize
    let tasks ← chunks.mapM (fun chunk =>
      IO.asTask (prio := Task.Priority.dedicated) <|
        observeBatchSerial chunk timeoutSeconds)
    let mut merged : List ProofStateResult := []
    for task in tasks do
      let chunkRows ← IO.ofExcept task.get
      merged := merged ++ chunkRows
    return merged

def recheckProofScript
    (goal : String)
    (proofScript : List (String × String))
    (timeoutSeconds : Nat := 45) : IO Bool := do
  let goalExpr := sanitizeGoalExpr goal
  if goalExpr.isEmpty then
    return false
  let tactics :=
    (proofScript.map Prod.snd).map String.trim |>.filter (fun t => !t.isEmpty)
  if tactics.isEmpty then
    return false
  let wrapper ← writeProofScriptWrapper goalExpr tactics
  let out ← runWrapperWithTimeout wrapper timeoutSeconds
  return out.exitCode == 0

end DifferentiableATP
end ATP
end HeytingLean
