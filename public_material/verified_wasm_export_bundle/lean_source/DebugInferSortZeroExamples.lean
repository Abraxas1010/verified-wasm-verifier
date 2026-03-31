import Lean
import Lean.Data.Json
import HeytingLean.CLI.SKYStageCore
import HeytingLean.LoF.Combinators.BracketAbstraction
import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.LeanKernel.Environment
import HeytingLean.LoF.LeanKernel.EnvironmentSKY
import HeytingLean.LoF.LeanKernel.FullKernelSKY
import HeytingLean.LoF.LeanKernel.InferSKY

open Lean

namespace HeytingLean.DebugInferSortZeroExamples

open HeytingLean.CLI.SKYStageCore
open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.LeanKernel

abbrev SExpr := LeanKernel.Expr Nat Unit Unit Unit
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
    (name : Name) : IO (Except String Lean.Expr) := do
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
        pure <| loweredResult.map eraseConstLevelInsts

private def mkConstDecl
    (nameId : Nat)
    (ty : SExpr) : Environment.ConstDecl Nat Unit Unit Unit :=
  Environment.ConstDecl.ofType nameId ty

private def litTypeComb (natTy stringTy : SExpr) : WHNFSKY.L :=
  let natTyL := EnvironmentSKY.Enc.expr natTy
  let stringTyL := EnvironmentSKY.Enc.expr stringTy
  let natCase := WHNFSKY.L.lam "n" <| WHNFSKY.optSome natTyL
  let stringCase := WHNFSKY.L.lam "s" <| WHNFSKY.optSome stringTyL
  WHNFSKY.L.lam "l" <|
    WHNFSKY.L.app2 (WHNFSKY.L.v "l") natCase stringCase

private def compileLitAwareInferComb
    (natTy stringTy : SExpr) : Except String Comb := do
  let litTypeL := litTypeComb natTy stringTy
  let inferL : WHNFSKY.L :=
    WHNFSKY.L.lam2 "env" "rules" <|
      let whnf := WHNFSKY.L.app2 FullKernelSKY.whnfFromEnvRules (WHNFSKY.L.v "env") (WHNFSKY.L.v "rules")
      let isDefEq := DefEqSKY.isDefEqSkyWith whnf
      let constType? := WHNFSKY.L.app FullKernelSKY.constTypeFromEnv (WHNFSKY.L.v "env")
      InferSKY.inferSkyWith constType? litTypeL whnf isDefEq
  match Bracket.Lam.compileClosedWithMode? .classic inferL with
  | some inferC => pure inferC
  | none => throw "failed to compile lit-aware infer kernel"

private def compileLitAwareInferSortZeroComb : Except String Comb := do
  match FullKernelSKY.inferIsSomeSortZeroFullWithLitTypeIdsComb? with
  | some v => pure v
  | none => throw "failed to compile lit-aware infer-sort-zero kernel"

private def mkSurfaces
    (env : Lean.Environment)
    (target : Lean.Expr) :
    IO (Except String (SExpr × Environment.Env Nat Unit Unit Unit × SExpr × SExpr)) := do
  let loweredTargetResult ← lowerProjExpr env target
  match loweredTargetResult with
  | .error err => pure (.error err)
  | .ok loweredTarget =>
      match collectConstLevelInsts loweredTarget with
      | .error err => pure (.error err)
      | .ok targetInsts =>
          let loweredTarget := eraseConstLevelInsts loweredTarget
          let seedNames := (collectConstRefs loweredTarget).toList
          match stageExprWithState default loweredTarget with
          | .error err => pure (.error err)
          | .ok (targetExpr, stAfterTarget) =>
              let natConst : Lean.Expr := .const ``Nat []
              let stringConst : Lean.Expr := .const ``String []
              match stageExprWithState stAfterTarget natConst with
              | .error err => pure (.error err)
              | .ok (natTy, stAfterNat) =>
                  match stageExprWithState stAfterNat stringConst with
                  | .error err => pure (.error err)
                  | .ok (stringTy, stAfterString) =>
                      let mut st := stAfterString
                      let mut decls : List (Environment.ConstDecl Nat Unit Unit Unit) := []
                      for name in seedNames do
                        let loweredTyResult ← lowerConstTypeWithInsts env targetInsts name
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
                      pure (.ok (targetExpr, envData, natTy, stringTy))

private def exprNat (n : Nat) : Lean.Expr :=
  .lit (.natVal n)

private def eqNat (a b : Nat) : Lean.Expr :=
  mkApp3 (.const ``Eq [Level.zero]) (.const ``Nat []) (exprNat a) (exprNat b)

private def runExample (label : String) (target : Lean.Expr) : IO Json := do
  let env ← importModules #[{module := `Init}] {} 0
  match (← mkSurfaces env target) with
  | .error err => pure <| Json.mkObj [("label", Json.str label), ("error", Json.str err)]
  | .ok (targetExpr, envData, natTy, stringTy) =>
      let some envC := EnvironmentSKY.envCombWithMode? .classic [] envData
        | pure <| Json.mkObj [("label", Json.str label), ("error", Json.str "failed to compile environment")]
      let some fullC := FullKernelSKY.compileFullWithMode? .classic
        | pure <| Json.mkObj [("label", Json.str label), ("error", Json.str "failed to compile full kernel bundle")]
      let some fuelC := FullKernelSKY.encodeNatCombWithMode? .classic 40
        | pure <| Json.mkObj [("label", Json.str label), ("error", Json.str "failed to compile fuel")]
      let some targetC := FullKernelSKY.compileExprNatUnitWithMode? .classic targetExpr
        | pure <| Json.mkObj [("label", Json.str label), ("error", Json.str "failed to compile target expr")]
      match compileLitAwareInferComb natTy stringTy, compileLitAwareInferSortZeroComb with
      | .ok inferC, .ok inferSortZeroC =>
          let inferOutOpt :=
            SKYExec.reduceFuel 400000 <|
              Comb.app
                (Comb.app
                  (Comb.app
                    (Comb.app
                      (Comb.app inferC envC)
                      fullC.emptyRules)
                    fuelC)
                  fullC.emptyCtx)
                targetC
          let inferTag := FullKernelSKY.decodeOptExprTagFuel 400000 inferOutOpt
          let inferSortZeroBool :=
            SKYExec.decodeChurchBoolFuel 400000 <|
              Comb.app
                (Comb.app
                  (Comb.app
                    (Comb.app
                      (Comb.app inferSortZeroC envC)
                      fullC.emptyRules)
                    fuelC)
                  fullC.emptyCtx)
                targetC
          pure <| Json.mkObj
            [ ("label", Json.str label)
            , ("infer_tag", match inferTag with | some s => Json.str s | none => Json.null)
            , ("infer_sort_zero_bool", Option.elim inferSortZeroBool Json.null Json.bool)
            ]
      | .error err, _ => pure <| Json.mkObj [("label", Json.str label), ("error", Json.str err)]
      | _, .error err => pure <| Json.mkObj [("label", Json.str label), ("error", Json.str err)]

def main (_args : List String) : IO UInt32 := do
  let examples := [("eq7_7", eqNat 7 7), ("eq0_1", eqNat 0 1)]
  let mut out : Array Json := #[]
  for (label, target) in examples do
    out := out.push (← runExample label target)
  IO.println (Json.pretty (Json.arr out))
  pure 0

end HeytingLean.DebugInferSortZeroExamples

def main (args : List String) : IO UInt32 :=
  HeytingLean.DebugInferSortZeroExamples.main args
