import Lean
import Lean.Data.Json
import HeytingLean.CLI.SKYStageCore
import HeytingLean.LoF.Combinators.BracketAbstraction
import HeytingLean.LoF.LeanKernel.DefEq
import HeytingLean.LoF.LeanKernel.Environment
import HeytingLean.LoF.LeanKernel.EnvironmentSKY
import HeytingLean.LoF.LeanKernel.FullKernelSKY
import HeytingLean.LoF.LeanKernel.Infer
import HeytingLean.LoF.LeanKernel.InferSKY

open Lean

namespace HeytingLean.DebugInferTypeSortNative

open HeytingLean.CLI.SKYStageCore
open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.LeanKernel

abbrev SExpr := LeanKernel.Expr Nat Unit Unit Unit
abbrev SCfg := Infer.Config Nat Unit Unit Unit
abbrev SCtx := Infer.Ctx Nat Unit Unit Unit
abbrev LevelInstMap := Std.HashMap Name (List Lean.Level)

private def collectConstRefs (e : Lean.Expr) (acc : Std.HashSet Name := {}) : Std.HashSet Name :=
  match e with
  | .const n _ => acc.insert n
  | .app f a => collectConstRefs a (collectConstRefs f acc)
  | .lam _ ty body _ => collectConstRefs body (collectConstRefs ty acc)
  | .forallE _ ty body _ => collectConstRefs body (collectConstRefs ty acc)
  | .letE _ ty val body _ => collectConstRefs body (collectConstRefs val (collectConstRefs ty acc))
  | .mdata _ body => collectConstRefs body acc
  | .proj _ _ body => collectConstRefs body acc
  | _ => acc

private def registerConstLevelInst
    (insts : LevelInstMap)
    (name : Name)
    (us : List Lean.Level) : Except String LevelInstMap :=
  match insts.get? name with
  | none => pure (insts.insert name us)
  | some prev =>
      if prev == us then
        pure insts
      else if prev.isEmpty then
        pure (insts.insert name us)
      else if us.isEmpty then
        pure insts
      else
        throw s!"multiple universe instantiations for {name}: saw {reprStr prev} and {reprStr us}"

private partial def collectConstLevelInsts
    (e : Lean.Expr)
    (insts : LevelInstMap := {}) : Except String LevelInstMap :=
  match e with
  | .const n us => registerConstLevelInst insts n us
  | .app f a => do
      let insts' ← collectConstLevelInsts f insts
      collectConstLevelInsts a insts'
  | .lam _ ty body _ => do
      let insts' ← collectConstLevelInsts ty insts
      collectConstLevelInsts body insts'
  | .forallE _ ty body _ => do
      let insts' ← collectConstLevelInsts ty insts
      collectConstLevelInsts body insts'
  | .letE _ ty val body _ => do
      let insts' ← collectConstLevelInsts ty insts
      let insts'' ← collectConstLevelInsts val insts'
      collectConstLevelInsts body insts''
  | .mdata _ body => collectConstLevelInsts body insts
  | .proj _ _ body => collectConstLevelInsts body insts
  | _ => pure insts

private partial def eraseConstLevelInsts : Lean.Expr → Lean.Expr
  | .bvar idx => .bvar idx
  | .fvar fvarId => .fvar fvarId
  | .mvar m => .mvar m
  | .sort u => .sort u
  | .const n _ => .const n []
  | .app f a => .app (eraseConstLevelInsts f) (eraseConstLevelInsts a)
  | .lam n ty body bi => .lam n (eraseConstLevelInsts ty) (eraseConstLevelInsts body) bi
  | .forallE n ty body bi => .forallE n (eraseConstLevelInsts ty) (eraseConstLevelInsts body) bi
  | .letE n ty val body nonDep =>
      .letE n (eraseConstLevelInsts ty) (eraseConstLevelInsts val) (eraseConstLevelInsts body) nonDep
  | .lit lit => .lit lit
  | .mdata md body => .mdata md (eraseConstLevelInsts body)
  | .proj s idx body => .proj s idx (eraseConstLevelInsts body)

private def lowerConstTypeWithInsts
    (env : Lean.Environment)
    (insts : LevelInstMap)
    (name : Name)
    (eraseLevels : Bool) : IO (Except String Lean.Expr) := do
  match env.find? name with
  | none => pure (.error s!"unknown constant {name}")
  | some ci =>
      let chosenLevels :=
        match insts.get? name with
        | some us =>
            if us.isEmpty && !ci.levelParams.isEmpty then
              List.replicate ci.levelParams.length Lean.Level.zero
            else
              us
        | none => List.replicate ci.levelParams.length Lean.Level.zero
      if chosenLevels.length != ci.levelParams.length then
        pure (.error s!"while lowering {name}: expected {ci.levelParams.length} universe levels, got {chosenLevels.length}")
      else
        let scopedType := ci.type.instantiateLevelParams ci.levelParams chosenLevels
        let loweredResult ← lowerProjExpr env scopedType
        pure <|
          loweredResult.map fun lowered =>
            if eraseLevels then eraseConstLevelInsts lowered else lowered

private def mkConstDecl
    (nameId : Nat)
    (ty : SExpr) : Environment.ConstDecl Nat Unit Unit Unit :=
  Environment.ConstDecl.ofType nameId ty

private def litTypeComb (natTy stringTy : SExpr) : WHNFSKY.L :=
  let natTyL := EnvironmentSKY.Enc.expr natTy
  let stringTyL := EnvironmentSKY.Enc.expr stringTy
  WHNFSKY.L.lam "l" <|
    WHNFSKY.L.app2 (WHNFSKY.L.v "l") (WHNFSKY.optSome natTyL) (WHNFSKY.optSome stringTyL)

private def compileLitAwareInferComb
    (natTy stringTy : SExpr) : Except String Comb := do
  let _ := natTy
  let _ := stringTy
  match FullKernelSKY.inferFullWithLitTypeIdsComb? with
  | some inferC => pure inferC
  | none => throw "failed to compile lit-aware infer kernel"

private def mkCfgAndExpr
    (env : Lean.Environment)
    (target : Lean.Expr)
    (eraseLevels : Bool) :
    IO (Except String
      (SCfg × SExpr × Lean.Expr × List Name × Environment.Env Nat Unit Unit Unit × SExpr × SExpr)) := do
  let loweredTargetResult ← lowerProjExpr env target
  match loweredTargetResult with
  | .error err => pure (.error err)
  | .ok loweredTarget =>
      let targetInstsResult := collectConstLevelInsts loweredTarget
      match targetInstsResult with
      | .error err => pure (.error err)
      | .ok targetInsts =>
          let loweredTarget := if eraseLevels then eraseConstLevelInsts loweredTarget else loweredTarget
          let seedNames := (collectConstRefs loweredTarget).toList
          match stageExprWithState default loweredTarget with
          | .error err => pure (.error err)
          | .ok (targetExpr, stAfterTarget) =>
              let natConst : Lean.Expr := .const ``Nat []
              let stringConst : Lean.Expr := .const ``String []
              let natStage :=
                stageExprWithState stAfterTarget natConst
              match natStage with
              | .error err => pure (.error err)
              | .ok (natTy, stAfterNat) =>
                  match stageExprWithState stAfterNat stringConst with
                  | .error err => pure (.error err)
                  | .ok (stringTy, stAfterString) =>
                      let mut st := stAfterString
                      let mut decls : List (Environment.ConstDecl Nat Unit Unit Unit) := []
                      for name in seedNames do
                        let loweredTyResult ← lowerConstTypeWithInsts env targetInsts name eraseLevels
                        match loweredTyResult with
                        | .error err => return .error err
                        | .ok loweredTy =>
                            match stageExprWithState st loweredTy with
                            | .error err => return .error err
                            | .ok (stagedTy, st') =>
                                st := st'
                                match st.names.get? name with
                                | none => return .error s!"failed to intern constant name {name}"
                                | some nameId =>
                                    decls := mkConstDecl nameId stagedTy :: decls
                      let envData : Environment.Env Nat Unit Unit Unit :=
                        { beqName := fun a b => a == b
                          consts := decls.reverse }
                      let cfg : SCfg :=
                        { iotaRules := Inductive.IotaRules.empty
                          constType? := fun c _ => Environment.Env.constType? envData c []
                          constValue? := fun _ _ => none
                          litType? := fun lit =>
                            match lit with
                            | .natVal _ => some natTy
                            | .strVal _ => some stringTy }
                      pure (.ok (cfg, targetExpr, loweredTarget, seedNames, envData, natTy, stringTy))

private def nativeInferSortExpr (env : Lean.Environment) (target : Lean.Expr) : IO Lean.Expr := do
  runMetaAtEnv env <| Meta.inferType target

private def ulevelRepr : LeanKernel.ULevel Unit Unit → String
  | .zero => "zero"
  | .succ u => s!"succ({ulevelRepr u})"
  | .max a b => s!"max({ulevelRepr a},{ulevelRepr b})"
  | .imax a b => s!"imax({ulevelRepr a},{ulevelRepr b})"
  | .param _ => "param"
  | .mvar _ => "mvar"

private def modeJson
    (label : String)
    (cfg : SCfg)
    (targetExpr : SExpr)
    (loweredTarget : Lean.Expr)
    (expectedLowered : Lean.Expr)
    (seedNames : List Name)
    (envData : Environment.Env Nat Unit Unit Unit)
    (natTy stringTy : SExpr) : Json :=
  let inferred? := Infer.infer? cfg 40 Infer.Ctx.empty targetExpr
  let inferSort? := Infer.inferSort? cfg 40 Infer.Ctx.empty targetExpr
  let expectedLowered :=
    expectedLowered
  let expectedStaged? :=
    match stageExprWithState default expectedLowered with
    | .ok (e, _) => some e
    | .error _ => none
  let inferredMatchesExpected :=
    match inferred?, expectedStaged? with
    | some inferred, some expected =>
        DefEq.isDefEqWithDelta cfg.constValue? cfg.iotaRules 40 inferred expected
    | _, _ => false
  let machineSection :=
    match EnvironmentSKY.envCombWithMode? .classic [] envData,
          FullKernelSKY.emptyRulesCombWithMode? .classic,
          compileLitAwareInferComb natTy stringTy,
          FullKernelSKY.compileFullWithMode? .classic,
          FullKernelSKY.encodeNatCombWithMode? .classic 40,
          FullKernelSKY.compileExprNatUnitWithMode? .classic targetExpr,
          expectedStaged?.bind (FullKernelSKY.compileExprNatUnitWithMode? .classic)
    with
    | some envC, some rulesC, .ok inferC, some fullC, some fuelC, some targetC, some expectedC =>
        let outOpt :=
          SKYExec.reduceFuel 1200000 <|
            Comb.app
              (Comb.app
                (Comb.app
                  (Comb.app
                    (Comb.app inferC envC)
                    rulesC)
                  fuelC)
                fullC.emptyCtx)
              targetC
        let observedTag := FullKernelSKY.decodeOptExprTagFuel 1200000 outOpt
        let observedDefEq :=
          match FullKernelSKY.decodeOptExprCombFuel 1200000 outOpt with
          | some observedC =>
              FullKernelSKY.runIsDefEqFullCombFuelWith fullC 40 1200000 envC rulesC observedC expectedC
          | none => none
        Json.mkObj
          [ ("observed_tag",
              match observedTag with
              | some tag => Json.str tag
              | none => Json.null)
          , ("observed_defeq_expected",
              match observedDefEq with
              | some b => Json.bool b
              | none => Json.null)
          ]
    | _, _, _, _, _, _, _ =>
        Json.mkObj [("error", Json.str "failed to build machine-side diagnostic surface")]
  Json.mkObj
    [ ("mode", Json.str label)
    , ("seed_names", Json.arr (seedNames.map (fun n => Json.str n.toString)).toArray)
    , ("lowered_target_repr", Json.str (reprStr loweredTarget))
    , ("target_expr_repr", Json.str (reprStr targetExpr))
    , ("infer_repr",
        match inferred? with
        | some inferred => Json.str (reprStr inferred)
        | none => Json.null)
    , ("infer_sort",
        match inferSort? with
        | some u => Json.str (ulevelRepr u)
        | none => Json.null)
    , ("expected_infer_repr", Json.str (reprStr expectedLowered))
    , ("infer_defeq_expected", Json.bool inferredMatchesExpected)
    , ("machine", machineSection)
    ]

private def runDecl (declName : Name) : IO Json := do
  let env ← importModules #[{module := declName.getPrefix}] {} 0
  match env.find? declName with
  | none => pure <| Json.mkObj [("error", Json.str s!"unknown declaration {declName}")]
  | some ci => do
      let target := ci.type
      let nativeInferSort ← nativeInferSortExpr env target
      let loweredExpectedResult ← lowerProjExpr env nativeInferSort
      match loweredExpectedResult with
      | .error err => pure <| Json.mkObj [("error", Json.str err)]
      | .ok loweredExpected => do
          let keptResult ← mkCfgAndExpr env target false
          let erasedResult ← mkCfgAndExpr env target true
          pure <| Json.mkObj <|
            [ ("decl", Json.str declName.toString)
            , ("native_infer_sort_repr", Json.str (reprStr nativeInferSort))
            ] ++
            [ ("kept_levels",
                match keptResult with
                | .error err => Json.mkObj [("error", Json.str err)]
                | .ok (cfg, targetExpr, loweredTarget, seedNames, envData, natTy, stringTy) =>
                    modeJson "kept_levels" cfg targetExpr loweredTarget loweredExpected seedNames envData natTy stringTy)
            , ("erased_levels",
                match erasedResult with
                | .error err => Json.mkObj [("error", Json.str err)]
                | .ok (cfg, targetExpr, loweredTarget, seedNames, envData, natTy, stringTy) =>
                    modeJson "erased_levels" cfg targetExpr loweredTarget (eraseConstLevelInsts loweredExpected) seedNames envData natTy stringTy)
            ]

def main (args : List String) : IO UInt32 := do
  let parseName (s : String) : Name :=
    s.splitOn "." |>.foldl (init := Name.anonymous) fun n part => Name.str n part
  match args with
  | [decl] =>
      let json ← runDecl (parseName decl)
      IO.println (Json.pretty json)
      pure 0
  | _ =>
      IO.eprintln "usage: lake env lean --run DebugInferTypeSortNative.lean <Decl.Name>"
      pure 1

end HeytingLean.DebugInferTypeSortNative

def main (args : List String) : IO UInt32 :=
  HeytingLean.DebugInferTypeSortNative.main args
