import Lean.Data.Json
import Lean.Data.Json.Stream
import HeytingLean.CLI.SKYTraceJson
import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.Combinators.SKYMachineBounded
import HeytingLean.LoF.LeanKernel.FullKernelSKY
import HeytingLean.LoF.LeanKernel.WHNF
import HeytingLean.LoF.LeanKernel.Infer
import HeytingLean.LoF.LeanKernel.Environment
import HeytingLean.LoF.LeanKernel.EnvironmentSKY
import HeytingLean.LoF.LeanKernel.Lean4LeanSKY
import HeytingLean.LoF.LeanKernel.WHNFIotaSKY

/-!
# full_kernel_sky_demo (Phase 25)

Executable demo + cross-validation for the *full* computation-plane kernel:
- β/ζ/δ/ι WHNF via `FullKernelSKY`,
- definitional equality + inference/checking layered on top of that WHNF,
- cross-validated against the native reference implementations.

This executable now also supports single-case reducer exports so the benchmark
workload can measure bounded-machine traces over larger FullKernel-compiled
terms instead of only the earlier Phase 15 constructor-tag demos.
-/

namespace HeytingLean.CLI.FullKernelSKYMain

open System
open Lean

open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.LeanKernel

abbrev E : Type := Expr Nat Unit Unit Unit
abbrev OracleRef := _root_.Unit

inductive Case where
  | whnf
  | infer
  | check
  | all
deriving DecidableEq, Repr

instance : ToString Case where
  toString
    | .whnf => "whnf"
    | .infer => "infer"
    | .check => "check"
    | .all => "all"

structure Cfg where
  caseName : Case := .all
  subcase : Option String := none
  describeExport : Bool := false
  fuelWhnf : Nat := 20
  fuelDefEq : Nat := 20
  fuelInfer : Nat := 20
  fuelReduce : Nat := 400000
  maxNodes : Nat := 200000
  traceStride : Nat := 25
  exportFiles : Bool := false
  outDir : FilePath := "dist" / "full_kernel_sky_demo"
deriving Repr

structure CompiledContext where
  env : Environment.Env Nat Unit Unit Unit
  rules : Inductive.IotaRules Nat
  bundle : FullKernelSKY.FullCompiled
  envC : Comb
  rulesC : Comb

private def usage : String :=
  String.intercalate "\n"
    [ "Usage: full_kernel_sky_demo [--case all|whnf|infer|check] [--subcase NAME] [--fuel-whnf N] [--fuel-defeq N] [--fuel-infer N] [--fuel-reduce N] [--max-nodes N] [--trace-stride N] [--export] [--out DIR]"
    , ""
    , "Phase 25 demo: compile FullKernelSKY (β/ζ/δ/ι + Infer/Check) to SKY and cross-validate."
    , "With --subcase NAME, run one curated case and print a reducer-facing constructor tag."
    , "With --subcase NAME --export, also export bounded-machine machine/final/trace JSON."
    , "With --subcase NAME --describe-export, print the live SKY decode term and expected tag term as JSON."
    , ""
    , "Defaults:"
    , "  --case all"
    , "  --fuel-whnf 20"
    , "  --fuel-defeq 20"
    , "  --fuel-infer 20"
    , "  --fuel-reduce 400000"
    , "  --max-nodes 200000"
    , ""
    , "WHNF subcases:"
    , "  beta | zeta | iota_zero | iota_succ | delta_only | delta_then_iota | zeta_with_const"
    , ""
    , "Infer subcases:"
    , "  sort0 | idLam | nat_zero | nat_succ_zero"
    , ""
    , "Check subcases:"
    , "  sort0:sort1 | nat_zero:Nat | nat_succ_zero:Nat | delta_only:Nat"
    ]

private def parseArgs (argv : List String) : IO Cfg := do
  let rec go (cfg : Cfg) : List String → IO Cfg
    | [] => pure cfg
    | "--help" :: _ => do
        IO.println usage
        throw (IO.userError "help")
    | "--case" :: c :: rest =>
        match c with
        | "all" => go { cfg with caseName := .all } rest
        | "whnf" => go { cfg with caseName := .whnf } rest
        | "infer" => go { cfg with caseName := .infer } rest
        | "check" => go { cfg with caseName := .check } rest
        | _ => throw <| IO.userError s!"invalid --case value: {c}"
    | "--subcase" :: s :: rest =>
        go { cfg with subcase := some s } rest
    | "--fuel-whnf" :: n :: rest =>
        match n.toNat? with
        | some v => go { cfg with fuelWhnf := v } rest
        | none => throw <| IO.userError s!"invalid --fuel-whnf value: {n}"
    | "--fuel-defeq" :: n :: rest =>
        match n.toNat? with
        | some v => go { cfg with fuelDefEq := v } rest
        | none => throw <| IO.userError s!"invalid --fuel-defeq value: {n}"
    | "--fuel-infer" :: n :: rest =>
        match n.toNat? with
        | some v => go { cfg with fuelInfer := v } rest
        | none => throw <| IO.userError s!"invalid --fuel-infer value: {n}"
    | "--fuel-reduce" :: n :: rest =>
        match n.toNat? with
        | some v => go { cfg with fuelReduce := v } rest
        | none => throw <| IO.userError s!"invalid --fuel-reduce value: {n}"
    | "--max-nodes" :: n :: rest =>
        match n.toNat? with
        | some v => go { cfg with maxNodes := v } rest
        | none => throw <| IO.userError s!"invalid --max-nodes value: {n}"
    | "--trace-stride" :: n :: rest =>
        match n.toNat? with
        | some 0 => throw <| IO.userError s!"invalid --trace-stride value: {n}"
        | some v => go { cfg with traceStride := v } rest
        | none => throw <| IO.userError s!"invalid --trace-stride value: {n}"
    | "--export" :: rest =>
        go { cfg with exportFiles := true } rest
    | "--describe-export" :: rest =>
        go { cfg with describeExport := true } rest
    | "--out" :: d :: rest =>
        go { cfg with outDir := FilePath.mk d } rest
    | x :: _ =>
        throw <| IO.userError s!"unexpected argument: {x}\n\n{usage}"
  go {} argv

private def die (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure code

private def exprTag (e : E) : String :=
  match e with
  | .bvar _ => "bvar"
  | .mvar _ => "mvar"
  | .sort _ => "sort"
  | .const _ _ => "const"
  | .app _ _ => "app"
  | .lam _ _ _ _ => "lam"
  | .forallE _ _ _ _ => "forallE"
  | .letE _ _ _ _ _ => "letE"
  | .lit _ => "lit"

private def expectEq {α : Type} [BEq α] [ToString α] (label : String) (a b : α) : Except String Unit :=
  if a == b then
    .ok ()
  else
    .error s!"{label}: expected {toString a} == {toString b}"

private def mkOutDir (outDir : FilePath) : IO (Except String Unit) := do
  try
    IO.FS.createDirAll outDir
    pure (Except.ok ())
  catch e =>
    pure (Except.error s!"failed to create output directory {outDir}: {e}")

private def writeFileSafe (path : FilePath) (contents : String) : IO Unit := do
  IO.FS.writeFile path contents

private def writeJsonFileSafe (path : FilePath) (payload : Json) : IO Unit := do
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  let s := IO.FS.Stream.ofHandle h
  s.writeJson payload
  s.putStr "\n"
  s.flush

private def nodeToJson (n : SKYGraph.Node OracleRef) : Json :=
  match n with
  | .combK => Json.mkObj [("tag", Json.str "K")]
  | .combS => Json.mkObj [("tag", Json.str "S")]
  | .combY => Json.mkObj [("tag", Json.str "Y")]
  | .app f a => Json.mkObj [("tag", Json.str "app"), ("f", toJson f), ("a", toJson a)]
  | .oracle _ => Json.mkObj [("tag", Json.str "oracle")]

private def stateToJson (maxNodes fuel : Nat) (s : SKYMachineBounded.State OracleRef) : Json :=
  Json.mkObj
    [ ("maxNodes", toJson maxNodes)
    , ("fuel", toJson fuel)
    , ("nodesUsed", toJson s.nodes.size)
    , ("focus", toJson s.focus)
    , ("stack", toJson s.stack.toArray)
    , ("nodes", Json.arr (s.nodes.map nodeToJson))
    ]

private def stateSummaryToJson (maxNodes fuel : Nat) (s : SKYMachineBounded.State OracleRef) : Json :=
  Json.mkObj
    [ ("maxNodes", toJson maxNodes)
    , ("fuel", toJson fuel)
    , ("nodesUsed", toJson s.nodes.size)
    , ("focus", toJson s.focus)
    , ("stackDepth", toJson s.stack.length)
    ]

private def traceSummaryToJson (step : Nat) (s : SKYMachineBounded.State OracleRef) : Json :=
  let reachable := SKYTraceJson.reachableIds s
  let active := SKYTraceJson.activeIds s reachable
  Json.mkObj
    [ ("step", toJson step)
    , ("nodesUsed", toJson s.nodes.size)
    , ("reachableNodes", toJson reachable.length)
    , ("activeRedexes", toJson active.length)
    , ("focus", toJson s.focus)
    , ("stackDepth", toJson s.stack.length)
    ]

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

inductive ExportTagKind where
  | expr
  | bool
deriving DecidableEq, Repr

private def tagTermToString? (kind : ExportTagKind) (t : Comb) : Option String :=
  match kind with
  | .expr =>
      let tagBVar := Comb.K
      let tagMVar := Comb.S
      let tagSort := Comb.Y
      let tagConst := Comb.app Comb.K Comb.K
      let tagApp := Comb.app Comb.K Comb.S
      let tagLam := Comb.app Comb.K Comb.Y
      let tagForall := Comb.app Comb.S Comb.K
      let tagLet := Comb.app Comb.S Comb.S
      let tagLit := Comb.app Comb.S Comb.Y
      if t = tagBVar then
        some "bvar"
      else if t = tagMVar then
        some "mvar"
      else if t = tagSort then
        some "sort"
      else if t = tagConst then
        some "const"
      else if t = tagApp then
        some "app"
      else if t = tagLam then
        some "lam"
      else if t = tagForall then
        some "forallE"
      else if t = tagLet then
        some "letE"
      else if t = tagLit then
        some "lit"
      else
        none
  | .bool =>
      if t = Comb.K then
        some "true"
      else if t = Comb.S then
        some "false"
      else
        none

private partial def combSurfaceChars : Comb → List Char → List Char
  | .K, acc => 'K' :: acc
  | .S, acc => 'S' :: acc
  | .Y, acc => 'Y' :: acc
  | .app fn arg, acc =>
      '(' :: combSurfaceChars fn (' ' :: combSurfaceChars arg (')' :: acc))

private def combSurface (t : Comb) : String :=
  String.mk (combSurfaceChars t [])

structure SingleExportCase where
  label : String
  decodeTerm : Comb
  expectedTagTerm : Comb
  tagKind : ExportTagKind
  fuelReduce : Nat

structure SingleExportRun where
  label : String
  decodeTermRepr : String
  observedTag : String
  expectedTag : String
  expectedTagTermRepr : String
  machineJson : Json
  finalJson : Json
  traceJson : Json
  stepsTaken : Nat
  maxStack : Nat
  maxNodesUsed : Nat
  traceSamples : Nat

/-! ## Environment + rules shared by all Phase 25 cases -/

private def mkCasesOnSpec : Inductive.CasesOnSpec Nat :=
  { recursor := 100
    numParams := 1
    ctors :=
      [ { name := 101, numFields := 0 }
      , { name := 102, numFields := 1 } ] }

private def mkRules : Inductive.IotaRules Nat :=
  { beqName := Nat.beq
    casesOnSpecs := [mkCasesOnSpec] }

private def mkRulesL : WHNFSKY.L :=
  let specL := WHNFIotaSKY.Enc.casesOnSpec 100 1 [ (101, 0), (102, 1) ]
  WHNFIotaSKY.Enc.iotaRules [specL]

private def mkEnv : Environment.Env Nat Unit Unit Unit :=
  let us : List (ULevel Unit Unit) := []
  let natName : Nat := 200
  let natTy : E := .const natName us
  let natZero : E := .const 101 us
  let natSucc : E := .const 102 us
  let natSuccTy : E := .forallE 0 .default natTy natTy

  let casesOn : E := .const 100 us
  let motive : E := .sort .zero
  let zCase : E := .lit (.natVal 0)
  let sCase : E := .lam 0 .default (.sort .zero) (.bvar 0)
  let n : E := .lit (.natVal 7)
  let majorSucc : E := .app natSucc n
  let deltaThenIotaBody : E := .app (.app (.app (.app casesOn motive) zCase) sCase) majorSucc

  { beqName := Nat.beq
    casesOnSpecs := [mkCasesOnSpec]
    consts :=
      [ Environment.ConstDecl.ofType natName (.sort .zero)
      , Environment.ConstDecl.ofType 101 natTy
      , Environment.ConstDecl.ofType 102 natSuccTy
      , Environment.ConstDecl.ofType 100 (.sort .zero)
      , Environment.ConstDecl.ofDef 32 natTy natZero
      , Environment.ConstDecl.ofDef 30 (.sort .zero) deltaThenIotaBody ] }

/-! ## Curated test cases -/

private def mkCasesWhnf : List (String × E) :=
  let idLam : E := .lam 0 .default (.sort .zero) (.bvar 0)
  let arg : E := .lit (.natVal 3)
  let letId : E := .letE 0 .default (.sort .zero) arg (.bvar 0)

  let us : List (ULevel Unit Unit) := []
  let casesOn : E := .const 100 us
  let motive : E := .sort .zero
  let zCase : E := .lit (.natVal 0)
  let sCase : E := .lam 0 .default (.sort .zero) (.bvar 0)
  let n : E := .lit (.natVal 7)
  let majorZero : E := .const 101 us
  let majorSucc : E := .app (.const 102 us) n
  let mkCasesOn (major : E) : E :=
    .app (.app (.app (.app casesOn motive) zCase) sCase) major

  let natName : Nat := 200
  let natTy : E := .const natName us
  let letNatZero : E := .letE 0 .default natTy (.const 101 us) (.bvar 0)

  [ ("beta", .app idLam arg)
  , ("zeta", letId)
  , ("iota_zero", mkCasesOn majorZero)
  , ("iota_succ", mkCasesOn majorSucc)
  , ("delta_only", .const 32 us)
  , ("delta_then_iota", .const 30 us)
  , ("zeta_with_const", letNatZero)
  ]

private def mkCasesInfer : List (String × E) :=
  let us : List (ULevel Unit Unit) := []
  let sort0 : E := .sort .zero
  let idLam : E := .lam 0 .default (.sort (.succ .zero)) (.bvar 0)
  let natZero : E := .const 101 us
  let natSuccZero : E := .app (.const 102 us) natZero
  [ ("sort0", sort0)
  , ("idLam", idLam)
  , ("nat_zero", natZero)
  , ("nat_succ_zero", natSuccZero)
  ]

private def mkCasesCheck : List (String × E × E) :=
  let us : List (ULevel Unit Unit) := []
  let sort0 : E := .sort .zero
  let sort1 : E := .sort (.succ .zero)
  let natTy : E := .const 200 us
  let natZero : E := .const 101 us
  let natSuccZero : E := .app (.const 102 us) natZero
  let deltaOnly : E := .const 32 us
  [ ("sort0:sort1", sort0, sort1)
  , ("nat_zero:Nat", natZero, natTy)
  , ("nat_succ_zero:Nat", natSuccZero, natTy)
  , ("delta_only:Nat", deltaOnly, natTy)
  ]

/-! ## Cross-validation runners -/

private def runWhnfCase (cfg : Cfg) (k : FullKernelSKY.FullCompiled)
    (envC rulesC : Comb) (name : String) (env : Environment.Env Nat Unit Unit Unit) (rules : Inductive.IotaRules Nat) (e : E) :
    Except String Unit :=
  let direct :=
    WHNF.whnfWithDelta
      (fun c us => Environment.Env.constValue? (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) env c us)
      rules
      cfg.fuelWhnf
      e
  match FullKernelSKY.runWhnfFullCombFuelWith k cfg.fuelWhnf cfg.fuelReduce envC rulesC e,
        Lean4LeanSKY.Enc.compileExprNatUnit? direct with
  | some outC, some directC =>
      match FullKernelSKY.runIsDefEqFullCombFuelWith k cfg.fuelDefEq cfg.fuelReduce envC rulesC outC directC with
      | some true => .ok ()
      | some false =>
          match FullKernelSKY.runWhnfFullTagFuelWith k cfg.fuelWhnf cfg.fuelReduce envC rulesC e with
          | none => .error s!"whnf/{name}: SKY output mismatch (and tag decode failed)"
          | some tag => .error s!"whnf/{name}: SKY output mismatch (tag={tag}, expectedTag={exprTag direct})"
      | none => .error s!"whnf/{name}: SKY defeq bool decode failed"
  | none, _ => .error s!"whnf/{name}: SKY WHNF comb eval failed"
  | _, none => .error s!"whnf/{name}: failed to compile expected expression to Comb"

private def runInferCase (cfg : Cfg) (k : FullKernelSKY.FullCompiled)
    (envC rulesC : Comb) (name : String) (env : Environment.Env Nat Unit Unit Unit) (e : E) :
    Except String Unit :=
  let cfg0 := (Environment.Env.toInferConfig (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) env)
  let ctx0 : Infer.Ctx Nat Unit Unit Unit := .empty
  let direct := Infer.infer? (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cfg0 cfg.fuelInfer ctx0 e
  match FullKernelSKY.runInferFullOptCombFuelWith k cfg.fuelInfer cfg.fuelReduce envC rulesC e with
  | none => .error s!"infer/{name}: SKY infer comb eval failed"
  | some outOpt =>
      let skyTy? := FullKernelSKY.decodeOptExprCombFuel cfg.fuelReduce outOpt
      match direct, skyTy? with
      | none, none => .ok ()
      | some directTy, some skyTy =>
          match Lean4LeanSKY.Enc.compileExprNatUnit? directTy with
          | none => .error s!"infer/{name}: failed to compile expected type to Comb"
          | some directTyC =>
              match FullKernelSKY.runIsDefEqFullCombFuelWith k cfg.fuelDefEq cfg.fuelReduce envC rulesC skyTy directTyC with
              | some true => .ok ()
              | some false =>
                  match FullKernelSKY.runInferFullTagFuelWith k cfg.fuelInfer cfg.fuelReduce envC rulesC e with
                  | none => .error s!"infer/{name}: SKY type mismatch (and tag decode failed)"
                  | some st => .error s!"infer/{name}: SKY type mismatch (gotTag={st}, expectedTag={exprTag directTy})"
              | none => .error s!"infer/{name}: SKY defeq bool decode failed"
      | none, some _ => .error s!"infer/{name}: expected none, got some"
      | some _, none => .error s!"infer/{name}: expected some, got none"

private def runCheckCase (cfg : Cfg) (k : FullKernelSKY.FullCompiled)
    (envC rulesC : Comb) (name : String) (env : Environment.Env Nat Unit Unit Unit) (e ty : E) :
    Except String Unit :=
  let cfg0 := (Environment.Env.toInferConfig (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) env)
  let ctx0 : Infer.Ctx Nat Unit Unit Unit := .empty
  let direct := Infer.check (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cfg0 cfg.fuelInfer ctx0 e ty
  match FullKernelSKY.runCheckFullFuelWith k cfg.fuelInfer cfg.fuelReduce envC rulesC e ty with
  | none => .error s!"check/{name}: SKY bool decode failed"
  | some b => expectEq s!"check/{name}" b direct

def compileContext : Except String CompiledContext :=
  let env := mkEnv
  let rules := mkRules
  let us : List (ULevel Unit Unit) := []
  let rulesL := mkRulesL
  match FullKernelSKY.compileFull?, EnvironmentSKY.envComb? us env, WHNFIotaSKY.compileClosed? rulesL with
  | some bundle, some envC, some rulesC =>
      .ok
        { env := env
          rules := rules
          bundle := bundle
          envC := envC
          rulesC := rulesC }
  | none, _, _ => .error "[full_kernel_sky_demo] E-COMPILE: failed to compile FullKernelSKY bundle"
  | _, none, _ => .error "[full_kernel_sky_demo] E-COMPILE: failed to compile environment to SKY"
  | _, _, none => .error "[full_kernel_sky_demo] E-COMPILE: failed to compile iota rules to SKY"

def caseErrors (ctx : CompiledContext) (cfg : Cfg) : List String :=
  let whnfErrs :=
    if cfg.caseName == .whnf || cfg.caseName == .all then
      mkCasesWhnf.foldl (init := ([] : List String)) fun acc (nm, e) =>
        match runWhnfCase cfg ctx.bundle ctx.envC ctx.rulesC nm ctx.env ctx.rules e with
        | .ok () => acc
        | .error msg => msg :: acc
    else
      []

  let inferErrs :=
    if cfg.caseName == .infer || cfg.caseName == .all then
      mkCasesInfer.foldl (init := ([] : List String)) fun acc (nm, e) =>
        match runInferCase cfg ctx.bundle ctx.envC ctx.rulesC nm ctx.env e with
        | .ok () => acc
        | .error msg => msg :: acc
    else
      []

  let checkErrs :=
    if cfg.caseName == .check || cfg.caseName == .all then
      mkCasesCheck.foldl (init := ([] : List String)) fun acc (nm, e, ty) =>
        match runCheckCase cfg ctx.bundle ctx.envC ctx.rulesC nm ctx.env e ty with
        | .ok () => acc
        | .error msg => msg :: acc
    else
      []

  whnfErrs ++ inferErrs ++ checkErrs

private def lookupNamed {α : Type} (what : String) (name : String) (xs : List (String × α)) :
    Except String α := do
  match xs.find? (fun entry => entry.1 = name) with
  | some (_, value) => pure value
  | none => throw s!"unknown {what} --subcase: {name}"

private def lookupCheckCase (name : String) : Except String (E × E) := do
  match mkCasesCheck.find? (fun entry => entry.1 = name) with
  | some (_, e, ty) => pure (e, ty)
  | none => throw s!"unknown check --subcase: {name}"

private def buildCheckComb (ctx : CompiledContext) (cfg : Cfg) (e ty : E) :
    Except String Comb := do
  let fuelC ←
    match FullKernelSKY.encodeNatComb? cfg.fuelInfer with
    | some v => pure v
    | none => throw "internal error: failed to encode infer fuel"
  let eC ←
    match FullKernelSKY.compileExprNatUnit? e with
    | some v => pure v
    | none => throw "internal error: failed to compile check expression to Comb"
  let tyC ←
    match FullKernelSKY.compileExprNatUnit? ty with
    | some v => pure v
    | none => throw "internal error: failed to compile check type to Comb"
  pure <|
    SKYExec.reduceFuel cfg.fuelReduce <|
      Comb.app
        (Comb.app
          (Comb.app
            (Comb.app
              (Comb.app
                (Comb.app ctx.bundle.check ctx.envC)
                ctx.rulesC)
              fuelC)
            ctx.bundle.emptyCtx)
          eC)
        tyC

private def encodeFuelComb (what : String) (n : Nat) : Except String Comb := do
  match FullKernelSKY.encodeNatComb? n with
  | some v => pure v
  | none => throw s!"internal error: failed to encode {what}"

private def compileExprComb (what : String) (e : E) : Except String Comb := do
  match FullKernelSKY.compileExprNatUnit? e with
  | some v => pure v
  | none => throw s!"internal error: failed to compile {what} to Comb"

private def buildSingleExportCase (ctx : CompiledContext) (cfg : Cfg) :
    Except String SingleExportCase := do
  let subcase ←
    match cfg.subcase with
    | some s => pure s
    | none => throw "--subcase NAME is required for single-case FullKernel execution"
  match cfg.caseName with
  | .all =>
      throw "--subcase cannot be combined with --case all"
  | .whnf =>
      let e ← lookupNamed "whnf" subcase mkCasesWhnf
      let direct :=
        WHNF.whnfWithDelta
          (fun c us => Environment.Env.constValue? (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) ctx.env c us)
          ctx.rules
          cfg.fuelWhnf
          e
      let fuelWhnfC ← encodeFuelComb "WHNF fuel" cfg.fuelWhnf
      let eC ← compileExprComb "WHNF expression" e
      let directC ← compileExprComb "expected WHNF expression" direct
      let outC :=
        Comb.app
          (Comb.app
            (Comb.app
              (Comb.app ctx.bundle.whnf ctx.envC)
              ctx.rulesC)
            fuelWhnfC)
          eC
      pure
        { label := s!"whnf/{subcase}"
          decodeTerm := Lean4LeanSKY.Decode.exprDecodeTerm outC
          expectedTagTerm := Lean4LeanSKY.Decode.exprTagTermFuel cfg.fuelReduce directC
          tagKind := .expr
          fuelReduce := cfg.fuelReduce }
  | .infer =>
      let e ← lookupNamed "infer" subcase mkCasesInfer
      let cfg0 := (Environment.Env.toInferConfig (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) ctx.env)
      let ctx0 : Infer.Ctx Nat Unit Unit Unit := .empty
      let directTy ←
        match Infer.infer? (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cfg0 cfg.fuelInfer ctx0 e with
        | some ty => pure ty
        | none => throw s!"infer/{subcase}: expected a type, got none"
      let fuelInferC ← encodeFuelComb "infer fuel" cfg.fuelInfer
      let eC ← compileExprComb "infer expression" e
      let directTyC ← compileExprComb "expected inferred type" directTy
      let outOpt :=
        Comb.app
          (Comb.app
            (Comb.app
              (Comb.app
                (Comb.app ctx.bundle.infer ctx.envC)
                ctx.rulesC)
              fuelInferC)
            ctx.bundle.emptyCtx)
          eC
      pure
        { label := s!"infer/{subcase}"
          decodeTerm := Lean4LeanSKY.Decode.exprDecodeTerm (Comb.app (Comb.app outOpt Comb.K) Comb.I)
          expectedTagTerm := Lean4LeanSKY.Decode.exprTagTermFuel cfg.fuelReduce directTyC
          tagKind := .expr
          fuelReduce := cfg.fuelReduce }
  | .check =>
      let (e, ty) ← lookupCheckCase subcase
      let cfg0 := (Environment.Env.toInferConfig (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) ctx.env)
      let ctx0 : Infer.Ctx Nat Unit Unit Unit := .empty
      let direct := Infer.check (Name := Nat) (Param := Unit) (MetaLevel := Unit) (MetaExpr := Unit) cfg0 cfg.fuelInfer ctx0 e ty
      let fuelInferC ← encodeFuelComb "check fuel" cfg.fuelInfer
      let eC ← compileExprComb "check expression" e
      let tyC ← compileExprComb "check type" ty
      let outBool :=
        Comb.app
          (Comb.app
            (Comb.app
              (Comb.app
                (Comb.app
                  (Comb.app ctx.bundle.check ctx.envC)
                  ctx.rulesC)
                fuelInferC)
              ctx.bundle.emptyCtx)
            eC)
          tyC
      pure
        { label := s!"check/{subcase}"
          decodeTerm := Comb.app (Comb.app outBool Comb.K) Comb.S
          expectedTagTerm := if direct then Comb.K else Comb.S
          tagKind := .bool
          fuelReduce := cfg.fuelReduce }

private partial def runExportWithStats
    (cfg : Cfg)
    (single : SingleExportCase)
    (chunkSize fuel : Nat)
    (s : SKYMachineBounded.State OracleRef)
    (stepsTaken maxStack maxNodesUsed : Nat)
    (traceRev : List Json) :
    Nat × Nat × Nat × List Json × String × SKYMachineBounded.State OracleRef :=
  let traceRev := traceSummaryToJson stepsTaken s :: traceRev
  if matchesCombSpine s s.focus s.stack single.expectedTagTerm then
    (stepsTaken, maxStack, maxNodesUsed, traceRev, "matched", s)
  else
    match fuel with
    | 0 =>
        (stepsTaken, maxStack, maxNodesUsed, traceRev, "fuelExhausted", s)
    | Nat.succ fuelPred =>
        let fuelChunk := Nat.min (Nat.succ fuelPred) chunkSize
        let run :=
          SKYMachineBounded.State.runFuelCount
            (OracleRef := OracleRef)
            oracleEvalFalse
            cfg.maxNodes
            fuelChunk
            s
        let stepsTaken' := stepsTaken + run.steps
        let maxStack' := Nat.max maxStack run.maxStack
        let maxNodesUsed' := Nat.max maxNodesUsed run.maxNodesUsed
        match run.status with
        | SKYMachineBounded.State.RunStatus.progress =>
            runExportWithStats
              cfg
              single
              chunkSize
              ((Nat.succ fuelPred) - fuelChunk)
              run.state
              stepsTaken'
              maxStack'
              maxNodesUsed'
              traceRev
        | SKYMachineBounded.State.RunStatus.halted =>
            let traceRev' := traceSummaryToJson stepsTaken' run.state :: traceRev
            if matchesCombSpine run.state run.state.focus run.state.stack single.expectedTagTerm then
              (stepsTaken', maxStack', maxNodesUsed', traceRev', "matched", run.state)
            else
              (stepsTaken', maxStack', maxNodesUsed', traceRev', "halted", run.state)
        | SKYMachineBounded.State.RunStatus.outOfHeap =>
            let traceRev' := traceSummaryToJson stepsTaken' run.state :: traceRev
            (stepsTaken', maxStack', maxNodesUsed', traceRev', "outOfHeap", run.state)

private def singleExportRunToJson (cfg : Cfg) (run : SingleExportRun) : Json :=
  Json.mkObj
    [ ("case_label", Json.str run.label)
    , ("decode_term", Json.str run.decodeTermRepr)
    , ("observed_tag", Json.str run.observedTag)
    , ("expected_tag", Json.str run.expectedTag)
    , ("expected_tag_term", Json.str run.expectedTagTermRepr)
    , ("machine", run.machineJson)
    , ("final", run.finalJson)
    , ("trace", run.traceJson)
    , ("config",
        Json.mkObj
          [ ("case_group", Json.str (toString cfg.caseName))
          , ("subcase", Json.str (cfg.subcase.getD ""))
          , ("fuel_whnf", toJson cfg.fuelWhnf)
          , ("fuel_defeq", toJson cfg.fuelDefEq)
          , ("fuel_infer", toJson cfg.fuelInfer)
          , ("fuel_reduce", toJson cfg.fuelReduce)
          , ("max_nodes", toJson cfg.maxNodes)
          , ("trace_stride", toJson cfg.traceStride)
          ])
    , ("steps_taken", toJson run.stepsTaken)
    , ("max_stack", toJson run.maxStack)
    , ("max_nodes_used", toJson run.maxNodesUsed)
    , ("trace_samples", toJson run.traceSamples)
    ]

private def singleExportCaseToJson (cfg : Cfg) (single : SingleExportCase) : Json :=
  Json.mkObj
    [ ("case_label", Json.str single.label)
    , ("case_group", Json.str (toString cfg.caseName))
    , ("subcase", Json.str (cfg.subcase.getD ""))
    , ("decode_term", Json.str (combSurface single.decodeTerm))
    , ("expected_tag_term", Json.str (combSurface single.expectedTagTerm))
    , ("decode_term_transport", Json.str "surface_sky_v1")
    , ("expected_tag_term_transport", Json.str "surface_sky_v1")
    , ("tag_kind",
        Json.str <|
          match single.tagKind with
          | .expr => "expr"
          | .bool => "bool")
    , ("fuel_reduce", toJson single.fuelReduce)
    ]

private def writeExportRunFiles (cfg : Cfg) (run : SingleExportRun) : IO UInt32 := do
  match (← mkOutDir cfg.outDir) with
  | .error msg => return (← die 2 s!"[full_kernel_sky_demo] E-OUTDIR: {msg}")
  | .ok () => pure ()

  let cfgPath := cfg.outDir / "config.repr.txt"
  let machinePath := cfg.outDir / "machine.json"
  let finalPath := cfg.outDir / "final.json"
  let tracePath := cfg.outDir / "trace.json"
  let expectedPath := cfg.outDir / "expected.txt"

  try
    writeFileSafe cfgPath (reprStr cfg ++ "\n")
    writeJsonFileSafe machinePath run.machineJson
    writeJsonFileSafe finalPath run.finalJson
    writeJsonFileSafe tracePath run.traceJson
    writeFileSafe expectedPath (String.intercalate "\n"
      [ s!"case_group={cfg.caseName}"
      , s!"subcase={(cfg.subcase.getD "")}"
      , s!"fuel_whnf={cfg.fuelWhnf}"
      , s!"fuel_defeq={cfg.fuelDefEq}"
      , s!"fuel_infer={cfg.fuelInfer}"
      , s!"fuel_reduce={cfg.fuelReduce}"
      , s!"max_nodes={cfg.maxNodes}"
      , s!"trace_stride={cfg.traceStride}"
      , s!"expected_tag={run.expectedTag}"
      , "decode_term_transport=surface_sky_v1"
      , s!"decode_term={run.decodeTermRepr}"
      , "expected_tag_term_transport=surface_sky_v1"
      , s!"expected_tag_term={run.expectedTagTermRepr}"
      , s!"steps_taken={run.stepsTaken}"
      , s!"max_stack={run.maxStack}"
      , s!"max_nodes_used={run.maxNodesUsed}"
      , s!"trace_samples={run.traceSamples}"
      ] ++ "\n")
  catch e =>
    return (← die 3 s!"[full_kernel_sky_demo] E-WRITE: failed to write outputs: {e}")

  IO.println s!"[full_kernel_sky_demo] wrote {machinePath}"
  IO.println s!"[full_kernel_sky_demo] wrote {finalPath}"
  IO.println s!"[full_kernel_sky_demo] wrote {tracePath}"
  IO.println s!"[full_kernel_sky_demo] ok"
  pure 0

private def runSingleTag (ctx : CompiledContext) (cfg : Cfg) : Except String String := do
  let subcase ←
    match cfg.subcase with
    | some s => pure s
    | none => throw "--subcase NAME is required for single-case FullKernel execution"
  match cfg.caseName with
  | .all =>
      throw "--subcase cannot be combined with --case all"
  | .whnf =>
      let e ← lookupNamed "whnf" subcase mkCasesWhnf
      match FullKernelSKY.runWhnfFullTagFuelWith ctx.bundle cfg.fuelWhnf cfg.fuelReduce ctx.envC ctx.rulesC e with
      | some tag => pure tag
      | none => throw s!"whnf/{subcase}: SKY WHNF tag eval failed"
  | .infer =>
      let e ← lookupNamed "infer" subcase mkCasesInfer
      match FullKernelSKY.runInferFullTagFuelWith ctx.bundle cfg.fuelInfer cfg.fuelReduce ctx.envC ctx.rulesC e with
      | some tag => pure tag
      | none => throw s!"infer/{subcase}: SKY infer tag eval failed"
  | .check =>
      let (e, ty) ← lookupCheckCase subcase
      match FullKernelSKY.runCheckFullFuelWith ctx.bundle cfg.fuelInfer cfg.fuelReduce ctx.envC ctx.rulesC e ty with
      | some true => pure "true"
      | some false => pure "false"
      | none => throw s!"check/{subcase}: SKY check bool eval failed"

private def runSingleExport (ctx : CompiledContext) (cfg : Cfg) : Except String SingleExportRun := do
  let single ← buildSingleExportCase ctx cfg
  let observedTag ← runSingleTag ctx cfg
  let s0 ←
    match SKYMachineBounded.State.compileComb? (OracleRef := OracleRef) cfg.maxNodes single.decodeTerm with
    | some s => pure s
    | none =>
        let required := SKYMachineBounded.State.requiredNodes single.decodeTerm
        throw
          s!"[full_kernel_sky_demo] out of heap during compilation; increase --max-nodes (currently {cfg.maxNodes}, required at least {required})"

  let chunkSize := Nat.max cfg.traceStride 1

  let (stepsTaken, maxStack, maxNodesUsed, traceRev, statusTag, finalState) :=
    runExportWithStats cfg single chunkSize single.fuelReduce s0 0 s0.stack.length s0.nodes.size []

  if statusTag = "outOfHeap" then
    throw s!"[full_kernel_sky_demo] machine ran out of heap (maxNodes={cfg.maxNodes}); increase --max-nodes"

  if statusTag ≠ "matched" then
    throw
      s!"[full_kernel_sky_demo] machine did not reach the expected tag term within --fuel-reduce={cfg.fuelReduce} (status={statusTag})"

  let machineJson := stateToJson cfg.maxNodes single.fuelReduce s0
  let finalJson := stateToJson cfg.maxNodes single.fuelReduce finalState
  let traceJson := Json.arr traceRev.reverse.toArray
  let expectedTag := (tagTermToString? single.tagKind single.expectedTagTerm).getD "unknown"
  pure
    { label := single.label
      decodeTermRepr := combSurface single.decodeTerm
      observedTag := observedTag
      expectedTag := expectedTag
      expectedTagTermRepr := combSurface single.expectedTagTerm
      machineJson := machineJson
      finalJson := finalJson
      traceJson := traceJson
      stepsTaken := stepsTaken
      maxStack := maxStack
      maxNodesUsed := maxNodesUsed
      traceSamples := traceRev.length }

private def runAll (cfg : Cfg) : IO UInt32 := do
  match compileContext with
  | .ok ctx =>
      let errs := caseErrors ctx cfg
      if errs.isEmpty then
        IO.println s!"[full_kernel_sky_demo] ok (case={cfg.caseName})"
        pure 0
      else
        for e in errs.reverse do
          IO.eprintln s!"[full_kernel_sky_demo] FAIL {e}"
        die 1 s!"[full_kernel_sky_demo] FAILED ({errs.length} failing case(s))"
  | .error err => die 2 err

private def runSingle (cfg : Cfg) : IO UInt32 := do
  match compileContext with
  | .error err => die 2 err
  | .ok ctx =>
      match buildSingleExportCase ctx cfg with
      | .error err => die 1 s!"[full_kernel_sky_demo] {err}"
      | .ok single =>
          if cfg.describeExport then
            IO.println (toString (singleExportCaseToJson cfg single))
            pure 0
          else
            match runSingleTag ctx cfg with
            | .error err => die 1 s!"[full_kernel_sky_demo] {err}"
            | .ok tag =>
                IO.println s!"[full_kernel_sky_demo] case={single.label}"
                IO.println s!"[full_kernel_sky_demo] tag={tag} tagTerm={reprStr single.expectedTagTerm}"
                if cfg.exportFiles then
                  match runSingleExport ctx cfg with
                  | .error err => die 1 err
                  | .ok run => writeExportRunFiles cfg run
                else
                  pure 0

private def serviceEmit (payload : Json) : IO Unit := do
  let h ← IO.getStdout
  h.putStrLn payload.compress
  h.flush

private def serviceGetString? (j : Json) (key : String) : Option String :=
  j.getObjValAs? String key |>.toOption

private def serviceGetNat? (j : Json) (key : String) : Option Nat :=
  j.getObjValAs? Nat key |>.toOption

private def serviceGetBool? (j : Json) (key : String) : Option Bool :=
  j.getObjValAs? Bool key |>.toOption

private def serviceParseCase? (raw : String) : Option Case :=
  match raw with
  | "whnf" => some .whnf
  | "infer" => some .infer
  | "check" => some .check
  | "all" => some .all
  | _ => none

private def serviceRequestIdField (requestId? : Option String) : List (String × Json) :=
  match requestId? with
  | some requestId => [("request_id", Json.str requestId)]
  | none => []

private def serviceErrorPayload (message : String) (requestId? : Option String := none) : Json :=
  Json.mkObj <|
    [ ("event", Json.str "error")
    , ("ok", Json.bool false)
    , ("error", Json.str message)
    ] ++ serviceRequestIdField requestId?

private def serviceCfgFromJson (base : Cfg) (request : Json) : Except String Cfg := do
  let caseName ←
    match serviceGetString? request "case" with
    | some raw =>
        match serviceParseCase? raw with
        | some caseName => pure caseName
        | none => throw s!"invalid case: {raw}"
    | none => pure base.caseName
  pure
    { caseName := caseName
      subcase := serviceGetString? request "subcase" <|> base.subcase
      fuelWhnf := (serviceGetNat? request "fuel_whnf").getD base.fuelWhnf
      fuelDefEq := (serviceGetNat? request "fuel_defeq").getD base.fuelDefEq
      fuelInfer := (serviceGetNat? request "fuel_infer").getD base.fuelInfer
      fuelReduce := (serviceGetNat? request "fuel_reduce").getD base.fuelReduce
      maxNodes := (serviceGetNat? request "max_nodes").getD base.maxNodes
      traceStride := (serviceGetNat? request "trace_stride").getD base.traceStride
      exportFiles := (serviceGetBool? request "export").getD base.exportFiles }

private def serviceResponsePayload
    (requestId? : Option String)
    (cfg : Cfg)
    (elapsedMs : Nat)
    (errs : List String) : Json :=
  Json.mkObj <|
    [ ("event", Json.str "response")
    , ("ok", Json.bool errs.isEmpty)
    , ("case", Json.str (toString cfg.caseName))
    , ("elapsed_ms", toJson elapsedMs)
    , ("errors", Json.arr <| errs.reverse.toArray.map Json.str)
    ] ++ serviceRequestIdField requestId?

private def serviceExportResponsePayload
    (requestId? : Option String)
    (cfg : Cfg)
    (elapsedMs : Nat)
    (result : Except String SingleExportRun) : Json :=
  match result with
  | .ok run =>
      Json.mkObj <|
        [ ("event", Json.str "response_export")
        , ("ok", Json.bool true)
        , ("case", Json.str (toString cfg.caseName))
        , ("subcase", Json.str (cfg.subcase.getD ""))
        , ("elapsed_ms", toJson elapsedMs)
        , ("export", singleExportRunToJson cfg run)
        ] ++ serviceRequestIdField requestId?
  | .error err =>
      Json.mkObj <|
        [ ("event", Json.str "response_export")
        , ("ok", Json.bool false)
        , ("case", Json.str (toString cfg.caseName))
        , ("subcase", Json.str (cfg.subcase.getD ""))
        , ("elapsed_ms", toJson elapsedMs)
        , ("error", Json.str err)
        ] ++ serviceRequestIdField requestId?

private def serviceDescribeExportPayload
    (requestId? : Option String)
    (cfg : Cfg)
    (elapsedMs : Nat)
    (result : Except String SingleExportCase) : Json :=
  match result with
  | .ok single =>
      Json.mkObj <|
        [ ("event", Json.str "response_describe_export")
        , ("ok", Json.bool true)
        , ("case", Json.str (toString cfg.caseName))
        , ("subcase", Json.str (cfg.subcase.getD ""))
        , ("elapsed_ms", toJson elapsedMs)
        , ("export_case", singleExportCaseToJson cfg single)
        ] ++ serviceRequestIdField requestId?
  | .error err =>
      Json.mkObj <|
        [ ("event", Json.str "response_describe_export")
        , ("ok", Json.bool false)
        , ("case", Json.str (toString cfg.caseName))
        , ("subcase", Json.str (cfg.subcase.getD ""))
        , ("elapsed_ms", toJson elapsedMs)
        , ("error", Json.str err)
        ] ++ serviceRequestIdField requestId?

private def serviceHandleRequest (ctx : CompiledContext) (request : Json) : IO (Bool × Json) := do
  let requestId? := serviceGetString? request "request_id"
  let command := (serviceGetString? request "command").getD "run"
  match command with
  | "ping" =>
      pure
        (true,
          Json.mkObj <|
            [ ("event", Json.str "pong")
            , ("ok", Json.bool true)
            ] ++ serviceRequestIdField requestId?)
  | "shutdown" =>
      pure
        (false,
          Json.mkObj <|
            [ ("event", Json.str "shutdown")
            , ("ok", Json.bool true)
            ] ++ serviceRequestIdField requestId?)
  | "run" =>
      match serviceCfgFromJson {} request with
      | .error err => pure (true, serviceErrorPayload err requestId?)
      | .ok cfg => do
          let startMs ← IO.monoMsNow
          let errs := caseErrors ctx cfg
          let endMs ← IO.monoMsNow
          pure (true, serviceResponsePayload requestId? cfg (endMs - startMs) errs)
  | "run_export" =>
      match serviceCfgFromJson { exportFiles := true } request with
      | .error err => pure (true, serviceErrorPayload err requestId?)
      | .ok cfg => do
          let startMs ← IO.monoMsNow
          let result := runSingleExport ctx cfg
          let endMs ← IO.monoMsNow
          pure (true, serviceExportResponsePayload requestId? cfg (endMs - startMs) result)
  | "describe_export" =>
      match serviceCfgFromJson {} request with
      | .error err => pure (true, serviceErrorPayload err requestId?)
      | .ok cfg => do
          let startMs ← IO.monoMsNow
          let result := buildSingleExportCase ctx cfg
          let endMs ← IO.monoMsNow
          pure (true, serviceDescribeExportPayload requestId? cfg (endMs - startMs) result)
  | other =>
      pure (true, serviceErrorPayload s!"unsupported command: {other}" requestId?)

private partial def serviceLoop (ctx : CompiledContext) : IO UInt32 := do
  let input ← IO.getStdin
  let rec go : IO UInt32 := do
    try
      let line ← input.getLine
      if line = "" then
        pure 0
      else
        let trimmed := line.trim
        if trimmed.isEmpty then
          go
        else
          match Json.parse trimmed with
          | .error err =>
              serviceEmit (serviceErrorPayload s!"json parse error: {err}")
              go
          | .ok request => do
              let (keepGoing, payload) ← serviceHandleRequest ctx request
              serviceEmit payload
              if keepGoing then go else pure 0
    catch e =>
      serviceEmit (serviceErrorPayload s!"service read failure: {e}")
      pure 1
  go

private def runService : IO UInt32 := do
  let startMs ← IO.monoMsNow
  serviceEmit <| Json.mkObj
    [ ("event", Json.str "booting")
    , ("ok", Json.bool true)
    , ("protocol", Json.str "full_kernel_sky_service/v2")
    , ("phase", Json.str "compile_context")
    ]
  match compileContext with
  | .error err =>
      serviceEmit (serviceErrorPayload err)
      pure 2
  | .ok ctx => do
      let endMs ← IO.monoMsNow
      serviceEmit <| Json.mkObj
        [ ("event", Json.str "ready")
        , ("ok", Json.bool true)
        , ("protocol", Json.str "full_kernel_sky_service/v2")
        , ("startup_ms", toJson (endMs - startMs))
        ]
      serviceLoop ctx

def main (argv : List String) : IO UInt32 := do
  if argv = ["--service"] then
    runService
  else
    try
      let cfg ← parseArgs argv
      if cfg.exportFiles && cfg.subcase.isNone then
        die 1 "[full_kernel_sky_demo] --export requires --subcase NAME"
      else if cfg.subcase.isSome then
        runSingle cfg
      else
        runAll cfg
    catch e =>
      match e with
      | .userError "help" => pure 0
      | _ => die 1 s!"[full_kernel_sky_demo] FAILED: {e}"

end HeytingLean.CLI.FullKernelSKYMain

open HeytingLean.CLI.FullKernelSKYMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.FullKernelSKYMain.main args
