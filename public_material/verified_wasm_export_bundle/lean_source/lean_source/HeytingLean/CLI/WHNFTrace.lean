import Lean
import Lean.Data.Json
import HeytingLean.CLI.LeanExprJson
import HeytingLean.CLI.SKYStageCore
import HeytingLean.CLI.SKYTraceJson
import HeytingLean.LoF.Combinators.BracketAbstraction
import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.Combinators.SKYMachineBounded
import HeytingLean.LoF.LeanKernel.DefEqSKY
import HeytingLean.LoF.LeanKernel.Lean4LeanSKY
import HeytingLean.LoF.LeanKernel.WHNFSKY

open Lean
open Lean.Meta

namespace HeytingLean.CLI.WHNFTrace

open HeytingLean.CLI.SKYStageCore
open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.LeanKernel

inductive TraceGrain where
  | step
  | whnf
  deriving DecidableEq, Inhabited, Repr

instance : ToString TraceGrain where
  toString
    | .step => "step"
    | .whnf => "whnf"

inductive WHNFKind where
  | beta
  | zeta
  | delta
  | iota
  | none
  deriving DecidableEq, Inhabited, Repr

instance : ToString WHNFKind where
  toString
    | .beta => "beta"
    | .zeta => "zeta"
    | .delta => "delta"
    | .iota => "iota"
    | .none => "none"

structure TraceCfg where
  fuelWhnf : Nat := 20
  fuelDefEq : Nat := 20
  fuelReduce : Nat := 400000
  maxNodes : Nat := 200000
  maxSteps : Nat := 256
  grain : TraceGrain := .step

structure TracedStep where
  seqId : Nat
  kind : WHNFKind
  input : Lean.Expr
  output : Lean.Expr

namespace StepVerify

abbrev L : Type := Bracket.Lam String

namespace L

def v (s : String) : L := Bracket.Lam.var s
def app (f a : L) : L := Bracket.Lam.app f a
def lam (x : String) (body : L) : L := Bracket.Lam.lam x body
def app2 (f a b : L) : L := app (app f a) b
def app3 (f a b c : L) : L := app (app2 f a b) c
def lam3 (a b c : String) (body : L) : L := lam a (lam b (lam c body))

end L

open L
open WHNFSKY (optCase fls whnfStepSky whnfSky)

def checkWhnfStepSky : L :=
  lam3 "fuel" "expected" "input" <|
    optCase (app whnfStepSky (v "input"))
      fls
      (lam "out" (app3 DefEqSKY.isDefEqSky (v "fuel") (v "out") (v "expected")))

def checkWhnfStepComb? : Option Comb :=
  Bracket.Lam.compileClosed? (Var := String) checkWhnfStepSky

def checkWhnfCallSky : L :=
  lam "whnfFuel" <|
    lam "defeqFuel" <|
      lam "expected" <|
        lam "input" <|
          app3 DefEqSKY.isDefEqSky
            (v "defeqFuel")
            (app2 whnfSky (v "whnfFuel") (v "input"))
            (v "expected")

def checkWhnfCallComb? : Option Comb :=
  Bracket.Lam.compileClosed? (Var := String) checkWhnfCallSky

def encodeNatComb? (n : Nat) : Option Comb :=
  WHNFSKY.encodeNatComb? n

end StepVerify

private def withElapsedMs (action : IO α) : IO (α × Nat) := do
  let startMs ← IO.monoMsNow
  let value ← action
  let endMs ← IO.monoMsNow
  pure (value, endMs - startMs)

private def boolTagTerm (b : Bool) : Comb :=
  if b then Comb.K else Comb.S

private def oracleEvalFalse : OracleRef → Bool := fun _ => false

private def matchesCombAt (s : SKYMachineBounded.State OracleRef) (id : Nat) : Comb → Bool
  | .K =>
      match s.node? id with
      | some .combK => true
      | _ => false
  | .S =>
      match s.node? id with
      | some .combS => true
      | _ => false
  | .Y =>
      match s.node? id with
      | some .combY => true
      | _ => false
  | .I => false
  | .app f a =>
      match s.node? id with
      | some (.app fId aId) => matchesCombAt s fId f && matchesCombAt s aId a
      | _ => false

private def combHeadArgsRev : Comb → Comb × List Comb
  | .app f a =>
      let (h, args) := combHeadArgsRev f
      (h, a :: args)
  | t => (t, [])

private def all2 (p : Nat → Comb → Bool) : List Nat → List Comb → Bool
  | [], [] => true
  | i :: is, t :: ts => p i t && all2 p is ts
  | _, _ => false

private def matchesCombSpine (s : SKYMachineBounded.State OracleRef) (focus : Nat) (stack : List Nat) (t : Comb) : Bool :=
  let (head, argsRev) := combHeadArgsRev t
  let args := argsRev.reverse
  matchesCombAt s focus head && all2 (fun i a => matchesCombAt s i a) stack args

private def runMachineExport
    (cfg : TraceCfg)
    (decodeTerm expectedTagTerm : Comb) : Except String (Json × Json × Json × Nat × Nat × Nat × Bool) := do
  let s0 <-
    match SKYMachineBounded.State.compileComb? (OracleRef := OracleRef) cfg.maxNodes decodeTerm with
    | some s => pure s
    | none => throw s!"out of heap during compilation; increase --max-nodes (currently {cfg.maxNodes})"

  let rec runWithStats (fuel : Nat) (s : SKYMachineBounded.State OracleRef)
      (stepsTaken maxStack maxNodesUsed : Nat) (traceRev : List Json) :
      Nat × Nat × Nat × List Json × SKYMachineBounded.State.StepResult OracleRef :=
    let traceRev := HeytingLean.CLI.SKYTraceJson.traceSampleToJson stepsTaken s :: traceRev
    match fuel with
    | 0 => (stepsTaken, maxStack, maxNodesUsed, traceRev, .halted s)
    | Nat.succ n =>
        match SKYMachineBounded.State.step (OracleRef := OracleRef) oracleEvalFalse cfg.maxNodes s with
        | .progress s' =>
            let maxStack' := Nat.max maxStack s'.stack.length
            let maxNodesUsed' := Nat.max maxNodesUsed s'.nodes.size
            runWithStats n s' (stepsTaken + 1) maxStack' maxNodesUsed' traceRev
        | .halted s' => (stepsTaken, maxStack, maxNodesUsed, traceRev, .halted s')
        | .outOfHeap s' => (stepsTaken, maxStack, maxNodesUsed, traceRev, .outOfHeap s')

  let (stepsTaken, maxStack, maxNodesUsed, traceRev, out) :=
    runWithStats cfg.fuelReduce s0 0 s0.stack.length s0.nodes.size []

  let finalState :=
    match out with
    | .progress s => s
    | .halted s => s
    | .outOfHeap s => s

  match out with
  | .outOfHeap _ =>
      throw s!"machine ran out of heap during reduction (maxNodes={cfg.maxNodes})"
  | _ => pure ()

  let matchesExpected := matchesCombSpine finalState finalState.focus finalState.stack expectedTagTerm
  let machineJson := stateToJson cfg.maxNodes cfg.fuelReduce s0
  let finalJson := stateToJson cfg.maxNodes cfg.fuelReduce finalState
  let traceJson := Json.arr traceRev.reverse.toArray
  pure (machineJson, finalJson, traceJson, stepsTaken, maxStack, maxNodesUsed, matchesExpected)

private def betaStep? (e : Lean.Expr) : Option Lean.Expr :=
  if e.isApp then
    let f := e.getAppFn
    if f.isLambda then
      some (f.betaRev e.getAppRevArgs)
    else
      none
  else
    none

private def zetaStep? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  match e with
  | .letE _ _ value body nondep =>
      let cfg ← getConfig
      if cfg.zeta && (!nondep || cfg.zetaHave) then
        pure (some (expandLet body #[value] (zetaHave := cfg.zetaHave)))
      else
        pure none
  | _ => pure none

private def iotaStep? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  match (← reduceMatcher? e) with
  | .reduced e' => pure (some e')
  | _ =>
      if !e.isApp then
        pure none
      else
        match e.getAppFn with
        | .const name _ =>
            match (← getEnv).find? name with
            | some (.recInfo _) | some (.quotInfo _) =>
                reduceRecMatcher? e
            | _ =>
                pure none
        | _ =>
            pure none

private def deltaStep? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let target :=
    if e.isApp then e.getAppFn else e
  match target with
  | .const name lvls =>
      match (← unfoldDefinition? e) with
      | none => pure none
      | some _ =>
          let some info := (← getEnv).find? name
            | pure none
          if !info.hasValue || info.levelParams.length != lvls.length then
            pure none
          else
            let body := info.instantiateValueLevelParams! lvls
            if e.isApp then
              pure (some (mkAppN body e.getAppArgs))
            else
              pure (some body)
  | _ =>
      pure none

/-- Classify and execute the next WHNF reduction step at the head of `e`.
This captures a strict subset of what `Meta.whnf` performs internally: zeta, beta,
iota (matcher/recursor), and delta (constant unfolding), plus recursion into app
functions.  Reductions that `Meta.whnf` handles but this stepper does not classify
include: Nat literal normalization, projection reduction already lowered away,
and structural simplifications inside non-head positions.  As a result,
`trace_matches_native_whnf` can be `false` even when `trace_complete` is `true`. -/
partial def nextWhnfStep? (e : Lean.Expr) : MetaM (Option (WHNFKind × Lean.Expr)) := do
  let e ← instantiateMVars e
  match ← zetaStep? e with
  | some e' => pure (some (.zeta, e'))
  | none =>
      match betaStep? e with
      | some e' => pure (some (.beta, e'))
      | none =>
          match ← iotaStep? e with
          | some e' => pure (some (.iota, e'))
          | none =>
              match ← deltaStep? e with
              | some e' => pure (some (.delta, e'))
              | none =>
                  if e.isApp then
                    let f := e.getAppFn
                    match ← nextWhnfStep? f with
                    | some (kind, f') => pure (some (kind, mkAppN f' e.getAppArgs))
                    | none => pure none
                  else
                    pure none

partial def traceExprSteps
    (e : Lean.Expr)
    (maxSteps : Nat)
    (seqStart : Nat := 0) : MetaM (Array TracedStep × Lean.Expr × Bool) := do
  let rec loop (current : Lean.Expr) (remaining : Nat) (seq : Nat) (acc : Array TracedStep) :
      MetaM (Array TracedStep × Lean.Expr × Bool) := do
    if remaining == 0 then
      return (acc, current, false)
    else
      match ← nextWhnfStep? current with
      | none => return (acc, current, true)
      | some (kind, next) =>
          let acc := acc.push { seqId := seq, kind, input := current, output := next }
          loop next (remaining - 1) (seq + 1) acc
  loop e maxSteps seqStart #[]

partial def nextBetaZetaWhnfStep? (e : Lean.Expr) : MetaM (Option (WHNFKind × Lean.Expr)) := do
  let e ← instantiateMVars e
  match ← zetaStep? e with
  | some e' => pure (some (.zeta, e'))
  | none =>
      match betaStep? e with
      | some e' => pure (some (.beta, e'))
      | none =>
          if e.isApp then
            let f := e.getAppFn
            match ← nextBetaZetaWhnfStep? f with
            | some (kind, f') => pure (some (kind, mkAppN f' e.getAppArgs))
            | none => pure none
          else
            pure none

partial def traceExprProjectedBetaZeta
    (e : Lean.Expr)
    (maxSteps : Nat)
    (seqStart : Nat := 0) : MetaM (Array TracedStep × Lean.Expr × Bool) := do
  let rec loop (current : Lean.Expr) (remaining : Nat) (seq : Nat) (acc : Array TracedStep) :
      MetaM (Array TracedStep × Lean.Expr × Bool) := do
    if remaining == 0 then
      return (acc, current, false)
    else
      match ← nextBetaZetaWhnfStep? current with
      | none => return (acc, current, true)
      | some (kind, next) =>
          let acc := acc.push { seqId := seq, kind, input := current, output := next }
          loop next (remaining - 1) (seq + 1) acc
  loop e maxSteps seqStart #[]

def buildStepVerificationJson
    (cfg : TraceCfg)
    (inputExpr outputExpr : Lean.Expr) : IO (Except String Json) := do
  match stageExprWithState {} inputExpr with
  | .error err => pure (.error err)
  | .ok (inputStaged, st1) =>
      match stageExprWithState st1 outputExpr with
      | .error err => pure (.error err)
      | .ok (outputStaged, _) =>
          match
            Lean4LeanSKY.Enc.compileExprNatUnit? inputStaged,
            Lean4LeanSKY.Enc.compileExprNatUnit? outputStaged,
            StepVerify.checkWhnfStepComb?,
            StepVerify.encodeNatComb? cfg.fuelDefEq
          with
          | some inputC, some outputC, some checkC, some fuelC =>
              let obligation := Comb.app (Comb.app (Comb.app checkC fuelC) outputC) inputC
              match
                SKYMachineBounded.State.compileComb? (OracleRef := OracleRef) cfg.maxNodes obligation,
                SKYMachineBounded.State.compileComb? (OracleRef := OracleRef) cfg.maxNodes (boolTagTerm true)
              with
              | some machineState, some expectedState =>
                  let machineJson := stateToJson cfg.maxNodes cfg.fuelReduce machineState
                  let finalJson := stateToJson cfg.maxNodes cfg.fuelReduce expectedState
                  let nodeCount :=
                    match machineJson.getObjValAs? Nat "nodesUsed" with
                    | .ok n => n
                    | .error _ => 0
                  pure <| .ok <| Json.mkObj
                    [ ("eligible", Json.bool true)
                    , ("node_count", toJson nodeCount)
                    , ("machine_json", machineJson)
                    , ("final_json", finalJson)
                    ]
              | _, _ =>
                  pure (.error s!"out of heap during per-step verifier compilation (maxNodes={cfg.maxNodes})")
          | _, _, _, _ =>
              pure (.error "failed to compile the WHNF-step SKY verifier inputs")

def buildWhnfVerificationJson
    (cfg : TraceCfg)
    (inputExpr outputExpr : Lean.Expr) : IO (Except String Json) := do
  match stageExprWithState {} inputExpr with
  | .error err => pure (.error err)
  | .ok (inputStaged, st1) =>
      match stageExprWithState st1 outputExpr with
      | .error err => pure (.error err)
      | .ok (outputStaged, _) =>
          match
            Lean4LeanSKY.Enc.compileExprNatUnit? inputStaged,
            Lean4LeanSKY.Enc.compileExprNatUnit? outputStaged,
            StepVerify.checkWhnfCallComb?,
            StepVerify.encodeNatComb? cfg.fuelWhnf,
            StepVerify.encodeNatComb? cfg.fuelDefEq
          with
          | some inputC, some outputC, some checkC, some fuelWhnfC, some fuelDefEqC =>
              let obligation :=
                Comb.app
                  (Comb.app
                    (Comb.app
                      (Comb.app checkC fuelWhnfC)
                      fuelDefEqC)
                    outputC)
                  inputC
              match
                SKYMachineBounded.State.compileComb? (OracleRef := OracleRef) cfg.maxNodes obligation,
                SKYMachineBounded.State.compileComb? (OracleRef := OracleRef) cfg.maxNodes (boolTagTerm true)
              with
              | some machineState, some expectedState =>
                  let machineJson := stateToJson cfg.maxNodes cfg.fuelReduce machineState
                  let finalJson := stateToJson cfg.maxNodes cfg.fuelReduce expectedState
                  let nodeCount :=
                    match machineJson.getObjValAs? Nat "nodesUsed" with
                    | .ok n => n
                    | .error _ => 0
                  pure <| .ok <| Json.mkObj
                    [ ("eligible", Json.bool true)
                    , ("node_count", toJson nodeCount)
                    , ("machine_json", machineJson)
                    , ("final_json", finalJson)
                    ]
              | _, _ =>
                  pure (.error s!"out of heap during WHNF-call verifier compilation (maxNodes={cfg.maxNodes})")
          | _, _, _, _, _ =>
              pure (.error "failed to compile the WHNF-call SKY verifier inputs")

private def traceStepJson
    (env : Lean.Environment)
    (_cfg : TraceCfg)
    (declName : Name)
    (role : String)
    (step : TracedStep) : IO Json := do
  let loweredInputResult ← lowerProjExpr env step.input
  let loweredOutputResult ← lowerProjExpr env step.output
  let inputExpr := loweredInputResult.toOption.getD step.input
  let outputExpr := loweredOutputResult.toOption.getD step.output
  let loweringError? :=
    match loweredInputResult, loweredOutputResult with
    | .error err, _ => some err
    | _, .error err => some err
    | _, _ => none
  let baseFields : List (String × Json) :=
    [ ("seq_id", toJson step.seqId)
    , ("decl_name", Json.str declName.toString)
    , ("trace_role", Json.str role)
    , ("kind", Json.str (toString step.kind))
    , ("input_expr_repr", Json.str (reprStr inputExpr))
    , ("output_expr_repr", Json.str (reprStr outputExpr))
    , ("input_expr_json", HeytingLean.CLI.LeanExprJson.exprToJson inputExpr)
    , ("output_expr_json", HeytingLean.CLI.LeanExprJson.exprToJson outputExpr)
    ]
  match step.kind with
  | .beta | .zeta =>
      match loweringError? with
      | some err =>
          pure <| Json.mkObj <| baseFields ++
            [ ("gpu_verifiable", Json.bool false)
            , ("eligible", Json.bool false)
            , ("skip_reason", Json.str err)
            ]
      | none =>
          pure <| Json.mkObj <| baseFields ++
            [ ("gpu_verifiable", Json.bool true)
            , ("verification_mode", Json.str "whnf_step")
            , ("eligible", Json.bool true)
            ]
  | _ =>
      pure <| Json.mkObj <| baseFields ++
        [ ("gpu_verifiable", Json.bool false)
        , ("eligible", Json.bool false)
        , ("skip_reason", Json.str s!"{step.kind} steps are native-only in Phase 2")
        ]

private def traceWhnfCallJson
    (env : Lean.Environment)
    (cfg : TraceCfg)
    (declName : Name)
    (role : String)
    (expr : Lean.Expr) : IO Json := do
  let loweredResult ← lowerProjExpr env expr
  match loweredResult with
  | .error err =>
      pure <| Json.mkObj
        [ ("decl_name", Json.str declName.toString)
        , ("trace_role", Json.str role)
        , ("trace_grain", Json.str (toString TraceGrain.whnf))
        , ("trace_complete", Json.bool false)
        , ("trace_error", Json.str err)
        ]
  | .ok lowered => do
      let ((steps, _fullFinalExpr, completed), traceElapsedMs) ← withElapsedMs <| runMetaAtEnv env do
        traceExprSteps lowered cfg.maxSteps
      let ((projectedSteps, projectedFinalExpr, projectedComplete), projectedElapsedMs) ← withElapsedMs <| runMetaAtEnv env do
        traceExprProjectedBetaZeta lowered cfg.maxSteps
      let nativeWhnfResult ← withElapsedMs <| runMetaAtEnv env do
        let out ← Meta.whnf lowered
        instantiateMVars out
      let (nativeFinal, nativeElapsedMs) := nativeWhnfResult
      let kindCounts :=
        steps.foldl (init := Std.HashMap.emptyWithCapacity) fun acc step =>
          let key := toString step.kind
          acc.insert key ((acc.getD key 0) + 1)
      let kindJson :=
        Json.mkObj <| ((kindCounts.toList.toArray.qsort (fun a b => a.1 < b.1)).toList.map fun (k, v) => (k, toJson v))
      let projectedKindCounts :=
        projectedSteps.foldl (init := Std.HashMap.emptyWithCapacity) fun acc step =>
          let key := toString step.kind
          acc.insert key ((acc.getD key 0) + 1)
      let projectedKindJson :=
        Json.mkObj <|
          ((projectedKindCounts.toList.toArray.qsort (fun a b => a.1 < b.1)).toList.map fun (k, v) => (k, toJson v))
      let projectedStepCount := projectedSteps.size
      let deltaIotaCount := (kindCounts.getD "delta" 0) + (kindCounts.getD "iota" 0)
      let verifyJson? ←
        if projectedStepCount > 0 then
          match (← buildWhnfVerificationJson cfg lowered projectedFinalExpr) with
          | .ok verifyJson => pure (some verifyJson)
          | .error err =>
              pure <| some <| Json.mkObj
                [ ("gpu_verifiable", Json.bool false)
                , ("eligible", Json.bool false)
                , ("skip_reason", Json.str err)
                ]
        else
          pure none
      let verifyFields :=
        match verifyJson? with
        | some verifyJson =>
            match verifyJson.getObj? with
            | .ok fields =>
                [ ("gpu_verifiable", Json.bool true) ] ++ fields.toList
            | .error _ =>
                [ ("gpu_verifiable", Json.bool false)
                , ("eligible", Json.bool false)
                , ("skip_reason", Json.str "internal verifier JSON was not an object")
                ]
        | none =>
            [ ("gpu_verifiable", Json.bool false)
            , ("eligible", Json.bool false)
            , ("skip_reason", Json.str "WHNF call contains no beta/zeta projection for GPU verification")
            ]
      pure <| Json.mkObj <|
        [ ("decl_name", Json.str declName.toString)
        , ("trace_role", Json.str role)
        , ("trace_grain", Json.str (toString TraceGrain.whnf))
        , ("trace_complete", Json.bool (completed && projectedComplete))
        , ("trace_elapsed_ms", toJson traceElapsedMs)
        , ("projected_trace_elapsed_ms", toJson projectedElapsedMs)
        , ("native_whnf_elapsed_ms", toJson nativeElapsedMs)
        , ("step_count", toJson steps.size)
        , ("kind_counts", kindJson)
        , ("projected_beta_zeta_steps", toJson projectedStepCount)
        , ("projected_kind_counts", projectedKindJson)
        , ("delta_iota_steps", toJson deltaIotaCount)
        , ("trace_matches_native_whnf", Json.bool (projectedFinalExpr == nativeFinal))
        , ("verification_mode", Json.str "whnf_call")
        , ("input_expr_repr", Json.str (reprStr lowered))
        , ("output_expr_repr", Json.str (reprStr projectedFinalExpr))
        , ("native_whnf_repr", Json.str (reprStr nativeFinal))
        , ("input_expr_json", HeytingLean.CLI.LeanExprJson.exprToJson lowered)
        , ("output_expr_json", HeytingLean.CLI.LeanExprJson.exprToJson projectedFinalExpr)
        , ("native_whnf_json", HeytingLean.CLI.LeanExprJson.exprToJson nativeFinal)
        ] ++ verifyFields

def traceDeclJson
    (env : Lean.Environment)
    (cfg : TraceCfg)
    (moduleName declName : Name)
    (declKind : String)
    (expr : Lean.Expr)
    (role : String) : IO Json := do
  match cfg.grain with
  | .whnf =>
      let inner ← traceWhnfCallJson env cfg declName role expr
      match inner.getObj? with
      | .ok fields =>
          pure <| Json.mkObj <|
            [ ("module", Json.str moduleName.toString)
            , ("decl_kind", Json.str declKind)
            ] ++ fields.toList
      | .error _ =>
          pure inner
  | .step =>
      let loweredResult ← lowerProjExpr env expr
      match loweredResult with
      | .error err =>
          pure <| Json.mkObj
            [ ("module", Json.str moduleName.toString)
            , ("decl_name", Json.str declName.toString)
            , ("decl_kind", Json.str declKind)
            , ("trace_role", Json.str role)
            , ("trace_grain", Json.str (toString TraceGrain.step))
            , ("trace_complete", Json.bool false)
            , ("trace_error", Json.str err)
            , ("steps", Json.arr #[])
            ]
      | .ok lowered => do
          let ((steps, finalExpr, completed), traceElapsedMs) ← withElapsedMs <| runMetaAtEnv env do
            traceExprSteps lowered cfg.maxSteps
          let nativeWhnfResult ← withElapsedMs <| runMetaAtEnv env do
            let out ← Meta.whnf lowered
            instantiateMVars out
          let (nativeFinal, nativeElapsedMs) := nativeWhnfResult
          let stepJsons ← steps.toList.mapM (traceStepJson env cfg declName role)
          let kindCounts :=
            steps.foldl (init := Std.HashMap.emptyWithCapacity) fun acc step =>
              let key := toString step.kind
              acc.insert key ((acc.getD key 0) + 1)
          let kindJson :=
            Json.mkObj <| ((kindCounts.toList.toArray.qsort (fun a b => a.1 < b.1)).toList.map fun (k, v) => (k, toJson v))
          pure <| Json.mkObj
            [ ("module", Json.str moduleName.toString)
            , ("decl_name", Json.str declName.toString)
            , ("decl_kind", Json.str declKind)
            , ("trace_role", Json.str role)
            , ("trace_grain", Json.str (toString TraceGrain.step))
            , ("trace_complete", Json.bool completed)
            , ("trace_elapsed_ms", toJson traceElapsedMs)
            , ("native_whnf_elapsed_ms", toJson nativeElapsedMs)
            , ("step_count", toJson steps.size)
            , ("kind_counts", kindJson)
            , ("trace_matches_native_whnf", Json.bool (finalExpr == nativeFinal))
            , ("final_expr_repr", Json.str (reprStr finalExpr))
            , ("native_whnf_repr", Json.str (reprStr nativeFinal))
            , ("final_expr_json", HeytingLean.CLI.LeanExprJson.exprToJson finalExpr)
            , ("native_whnf_json", HeytingLean.CLI.LeanExprJson.exprToJson nativeFinal)
            , ("steps", Json.arr stepJsons.toArray)
            ]

end HeytingLean.CLI.WHNFTrace
