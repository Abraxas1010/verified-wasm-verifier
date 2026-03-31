import Lean
import Lean.Data.Json
import HeytingLean.LoF.Combinators.SKYExec
import HeytingLean.LoF.Combinators.SKYMultiway
import HeytingLean.LoF.LeanKernel.Environment
import HeytingLean.LoF.LeanKernel.EnvironmentSKY
import HeytingLean.LoF.LeanKernel.FullKernelSKY
import HeytingLean.LoF.LeanKernel.WHNF
import HeytingLean.LoF.LeanKernel.WHNFIotaSKY

open Lean

namespace HeytingLean.CLI.DiffATPTopoCorpusMain

open HeytingLean.LoF
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.LeanKernel

abbrev E : Type := Expr Nat Unit Unit Unit

structure TopoNodeRow where
  nodeId : String
  termJson : Json
  termHash : String
  depth : Nat
deriving Inhabited

structure TopoEdgeRow where
  edgeId : String
  fromId : String
  toId : String
  ruleTag : String
  pathDirs : List String
deriving Inhabited

structure TargetWitness where
  witnessKind : String
  payload : Json
deriving Inhabited

structure TopoRow where
  rowId : String
  sourceKind : String
  sourceCommand : String
  rootComb : Json
  rootHash : String
  maxDepth : Nat
  nodes : Array TopoNodeRow
  edges : Array TopoEdgeRow
  traceSummary : Json
  targetWitness? : Option TargetWitness
  promotionTarget : String
  provenance : String
  tags : List String
deriving Inhabited

structure TopoCorpusReport where
  schema : String
  kind : String
  honestBoundary : String
  rowIds : Array String
  rows : Array TopoRow
deriving Inhabited

private def usage : String :=
  String.intercalate "\n"
    [ "Usage: diff_atp_topo_corpus [--output FILE]"
    , ""
    , "Emit the frozen differentiable-ATP topology corpus for SKY toy terms and"
    , "curated FullKernel WHNF exports."
    ]

private def parseArgs (argv : List String) : Except String (Option System.FilePath) := do
  let rec go (out : Option System.FilePath) : List String → Except String (Option System.FilePath)
    | [] => pure out
    | "--output" :: path :: rest => go (some (System.FilePath.mk path)) rest
    | "--help" :: _ => throw usage
    | x :: _ => throw s!"unexpected argument: {x}\n\n{usage}"
  go none argv

private def combToJson : Comb → Json
  | .K => Json.arr #[Json.num 0]
  | .S => Json.arr #[Json.num 1]
  | .Y => Json.arr #[Json.num 2]
  | .app f a => Json.arr #[Json.num 3, combToJson f, combToJson a]

private def combHashString (t : Comb) : String :=
  toString (hashComb t)

private def opaqueTermJson (hash : String) : Json :=
  Json.mkObj
    [ ("kind", Json.str "opaque_fullkernel_term")
    , ("term_hash", Json.str hash)
    ]

private def ruleTagString : Comb.RuleTag → String
  | .K => "K"
  | .S => "S"
  | .Y => "Y"

private def dirString : Comb.Dir → String
  | .L => "L"
  | .R => "R"

private def nodeRowToJson (row : TopoNodeRow) : Json :=
  Json.mkObj
    [ ("node_id", Json.str row.nodeId)
    , ("term_json", row.termJson)
    , ("term_hash", Json.str row.termHash)
    , ("depth", Json.num row.depth)
    ]

private def edgeRowToJson (row : TopoEdgeRow) : Json :=
  Json.mkObj
    [ ("edge_id", Json.str row.edgeId)
    , ("from_id", Json.str row.fromId)
    , ("to_id", Json.str row.toId)
    , ("rule_tag", Json.str row.ruleTag)
    , ("path_dirs", Json.arr <| row.pathDirs.toArray.map Json.str)
    ]

private def targetWitnessToJson (w : TargetWitness) : Json :=
  Json.mkObj
    [ ("witness_kind", Json.str w.witnessKind)
    , ("payload", w.payload)
    ]

private def rowToJson (row : TopoRow) : Json :=
  Json.mkObj
    [ ("row_id", Json.str row.rowId)
    , ("source_kind", Json.str row.sourceKind)
    , ("source_command", Json.str row.sourceCommand)
    , ("root_comb", row.rootComb)
    , ("root_hash", Json.str row.rootHash)
    , ("max_depth", Json.num row.maxDepth)
    , ("nodes", Json.arr <| row.nodes.map nodeRowToJson)
    , ("edges", Json.arr <| row.edges.map edgeRowToJson)
    , ("trace_summary", row.traceSummary)
    , ("target_witness", match row.targetWitness? with | some w => targetWitnessToJson w | none => Json.null)
    , ("promotion_target", Json.str row.promotionTarget)
    , ("provenance", Json.str row.provenance)
    , ("tags", Json.arr <| row.tags.toArray.map Json.str)
    ]

private def corpusToJson (report : TopoCorpusReport) : Json :=
  Json.mkObj
    [ ("schema", Json.str report.schema)
    , ("kind", Json.str report.kind)
    , ("honest_boundary", Json.str report.honestBoundary)
    , ("row_ids", Json.arr <| report.rowIds.map Json.str)
    , ("rows", Json.arr <| report.rows.map rowToJson)
    ]

private def parseNodeHashPayload? (payload : Json) : Option String := do
  match payload.getObj? with
  | .error _ => none
  | .ok obj =>
      match obj.get? "term_hash" with
      | none => none
      | some hashJson =>
          match hashJson.getStr? with
          | .ok s => some s
          | .error _ => none

private def findIdxFuel {α : Type} [DecidableEq α] (arr : Array α) (x : α) (fuel i : Nat) :
    Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if h : i < arr.size then
        if arr[i] = x then some i else findIdxFuel arr x fuel (i + 1)
      else
        none

private def findIdx {α : Type} [DecidableEq α] (arr : Array α) (x : α) : Option Nat :=
  findIdxFuel arr x (arr.size + 1) 0

private def dedupArray {α : Type} [DecidableEq α] (xs : Array α) : Array α :=
  xs.foldl (init := (#[] : Array α)) fun acc x =>
    if acc.contains x then acc else acc.push x

private def nodeIdOf (idx : Nat) : String :=
  s!"n{idx}"

private def edgeIdOf (idx : Nat) : String :=
  s!"e{idx}"

private def getIdxWithDepth (nodes : Array Comb) (depths : Array Nat) (x : Comb) (depth : Nat) :
    (Array Comb × Array Nat × Nat) :=
  match findIdx nodes x with
  | some i => (nodes, depths, i)
  | none => (nodes.push x, depths.push depth, nodes.size)

private structure BuiltGraph where
  nodes : Array TopoNodeRow
  edges : Array TopoEdgeRow
  traceSummary : Json

private def buildGraph (root : Comb) (maxDepth : Nat) : BuiltGraph := Id.run do
  let mut nodesRaw : Array Comb := #[root]
  let mut depths : Array Nat := #[0]
  let mut edges : Array TopoEdgeRow := #[]
  let mut levels : Array (Array Nat) := #[#[0]]
  let mut curr : Array Comb := #[root]
  let mut branchingNodes : Nat := 0

  for depth in [0:maxDepth] do
    let mut nextRaw : Array Comb := #[]
    for s in curr do
      let some srcIdx := findIdx nodesRaw s
        | unreachable!
      let outgoing := Comb.stepEdgesList s
      let childSet := dedupArray <| (outgoing.map (fun (_, t) => t)).toArray
      if childSet.size > 1 then
        branchingNodes := branchingNodes + 1
      for (ed, t) in outgoing do
        let (nodesRaw', depths', dstIdx) := getIdxWithDepth nodesRaw depths t (depth + 1)
        nodesRaw := nodesRaw'
        depths := depths'
        edges := edges.push
          { edgeId := edgeIdOf edges.size
            fromId := nodeIdOf srcIdx
            toId := nodeIdOf dstIdx
            ruleTag := ruleTagString ed.rule
            pathDirs := ed.path.map dirString }
        nextRaw := nextRaw.push t
    let next := dedupArray nextRaw
    let nextIdxs := next.map fun t =>
      let (_, _, idx) := getIdxWithDepth nodesRaw depths t (depth + 1)
      idx
    levels := levels.push nextIdxs
    curr := next

  let nodeRows :=
    (List.range nodesRaw.size).toArray.map fun idx =>
      match nodesRaw[idx]?, depths[idx]? with
      | some term, some depth =>
          { nodeId := nodeIdOf idx
            termJson := combToJson term
            termHash := combHashString term
            depth := depth }
      | _, _ => unreachable!
  let levelWidths := levels.map (fun lvl => Json.num lvl.size)
  let traceSummary :=
    Json.mkObj
      [ ("level_widths", Json.arr levelWidths)
      , ("node_count", Json.num nodeRows.size)
      , ("edge_count", Json.num edges.size)
      , ("branching_nodes", Json.num branchingNodes)
      ]
  { nodes := nodeRows, edges := edges, traceSummary := traceSummary }

private def buildExpectedWitnessWithJson (term : Comb) (termJson : Json) : TargetWitness :=
  { witnessKind := "expected_term"
    payload := Json.mkObj
      [ ("term_hash", Json.str (combHashString term))
      , ("term_json", termJson)
      ] }

private def buildExpectedWitness (term : Comb) : TargetWitness :=
  buildExpectedWitnessWithJson term (combToJson term)

private def buildPresentNodeWitness? (nodes : Array TopoNodeRow) (hash : String) : Option TargetWitness := do
  let row <- nodes.find? (fun node => node.termHash = hash)
  pure
    { witnessKind := "expected_term"
      payload := Json.mkObj
        [ ("term_hash", Json.str row.termHash)
        , ("term_json", row.termJson)
        , ("node_id", Json.str row.nodeId)
        ] }

private def validateUniqueIds (row : TopoRow) : Except String Unit := do
  let nodeIds := row.nodes.map (·.nodeId)
  if (dedupArray nodeIds).size != nodeIds.size then
    throw s!"{row.rowId}: duplicate node ids"
  let edgeIds := row.edges.map (·.edgeId)
  if (dedupArray edgeIds).size != edgeIds.size then
    throw s!"{row.rowId}: duplicate edge ids"

private def validateRootSingleRule (rowId expectedRule : String) (root : Comb) : Except String Unit := do
  let edges := Comb.stepEdgesList root
  if edges.length != 1 then
    throw s!"{rowId}: expected exactly one one-step reduction, got {edges.length}"
  match edges.head? with
  | some ({ rule := rule, path := [] }, _) =>
      if ruleTagString rule = expectedRule then
        pure ()
      else
        throw s!"{rowId}: expected root rule {expectedRule}, got {ruleTagString rule}"
  | some ({ path := path, .. }, _) =>
      throw s!"{rowId}: expected root-only reduction, found path length {path.length}"
  | none =>
      throw s!"{rowId}: missing reduction edge"

private def validateBranchPair (rowId : String) (root : Comb) : Except String Unit := do
  let succs : Array String := dedupArray <| ((Comb.stepEdgesList root).map (fun (_, t) => combHashString t)).toArray
  if succs.size >= 2 then
    pure ()
  else
    throw s!"{rowId}: expected at least two distinct one-step successors"

private def edgePairsFrom (edges : Array TopoEdgeRow) (fromId : String) : Array String :=
  edges.foldl (init := (#[] : Array String)) fun acc edge =>
    if edge.fromId = fromId then acc.push edge.toId else acc

private partial def reachableFrom
    (edges : Array TopoEdgeRow) (todo seen : List String) : List String :=
  match todo with
  | [] => seen
  | id :: rest =>
      if id ∈ seen then
        reachableFrom edges rest seen
      else
        let next := edgePairsFrom edges id
        reachableFrom edges (next.toList ++ rest) (id :: seen)

private def validateDiamondCandidate (row : TopoRow) : Except String Unit := do
  let first := dedupArray <| edgePairsFrom row.edges "n0"
  let rec findCommon : List String → Except String Unit
    | [] => throw s!"{row.rowId}: expected two one-step successors with a common descendant"
    | x :: xs =>
        let rx := reachableFrom row.edges [x] []
        let rec scan : List String → Except String Unit
          | [] => findCommon xs
          | y :: ys =>
              if x = y then
                scan ys
              else
                let ry := reachableFrom row.edges [y] []
                if rx.any (fun id => id ∈ ry) then
                  pure ()
                else
                  scan ys
        scan xs
  findCommon first.toList

private def validateSourceCommand (row : TopoRow) : Except String Unit := do
  if row.sourceCommand.trim.isEmpty then
    throw s!"{row.rowId}: source_command must be non-empty"

private def validateTargetWitnessPresence (row : TopoRow) : Except String Unit := do
  match row.targetWitness? with
  | none => pure ()
  | some witness =>
      match parseNodeHashPayload? witness.payload with
      | some hash =>
          if row.nodes.any (fun node => node.termHash = hash) || row.sourceKind = "fullkernel_export" then
            pure ()
          else
            throw s!"{row.rowId}: target witness hash not present in row nodes"
      | none => pure ()

private def validateRow (row : TopoRow) (root : Comb) : Except String Unit := do
  if row.nodes.isEmpty then
    throw s!"{row.rowId}: nodes must be non-empty"
  match row.nodes[0]? with
  | some rootNode =>
      if row.rootHash != rootNode.termHash then
        throw s!"{row.rowId}: root hash must match n0 term hash"
  | none =>
      throw s!"{row.rowId}: missing n0"
  validateUniqueIds row
  validateSourceCommand row
  validateTargetWitnessPresence row
  match row.rowId with
  | "toy_k_root_v1" => validateRootSingleRule row.rowId "K" root
  | "toy_s_root_v1" => validateRootSingleRule row.rowId "S" root
  | "toy_y_root_v1" => validateRootSingleRule row.rowId "Y" root
  | "toy_branch_pair_v1" => validateBranchPair row.rowId root
  | "toy_diamond_candidate_v1" =>
      validateBranchPair row.rowId root
      validateDiamondCandidate row
  | _ => pure ()

private def mkRow
    (rowId sourceKind sourceCommand promotionTarget provenance : String)
    (tags : List String)
    (root : Comb)
    (maxDepth : Nat)
    (targetWitness? : Option TargetWitness := none) : Except String TopoRow := do
  let built := buildGraph root maxDepth
  let row :=
    { rowId := rowId
      sourceKind := sourceKind
      sourceCommand := sourceCommand
      rootComb := combToJson root
      rootHash := combHashString root
      maxDepth := maxDepth
      nodes := built.nodes
      edges := built.edges
      traceSummary := built.traceSummary
      targetWitness? := targetWitness?
      promotionTarget := promotionTarget
      provenance := provenance
      tags := tags }
  validateRow row root
  pure row

/-! FullKernel shared environment copied from the curated Phase-25 demo so the corpus stays
aligned with the existing executable row family. -/

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
  let specL := WHNFIotaSKY.Enc.casesOnSpec 100 1 [(101, 0), (102, 1)]
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

private def lookupNamed {α : Type} (what : String) (name : String) (xs : List (String × α)) :
    Except String α := do
  match xs.find? (fun entry => entry.1 = name) with
  | some (_, value) => pure value
  | none => throw s!"unknown {what}: {name}"

private structure FullKernelContext where
  env : Environment.Env Nat Unit Unit Unit
  rules : Inductive.IotaRules Nat
  bundle : FullKernelSKY.FullCompiled
  envC : Comb
  rulesC : Comb

private def mkFullKernelContext : Except String FullKernelContext := do
  let env := mkEnv
  let rules := mkRules
  let us : List (ULevel Unit Unit) := []
  let rulesL := mkRulesL
  let some bundle := FullKernelSKY.compileFull?
    | throw "failed to compile FullKernelSKY bundle"
  let some envC := EnvironmentSKY.envComb? us env
    | throw "failed to compile FullKernel environment"
  let some rulesC := WHNFIotaSKY.compileClosed? rulesL
    | throw "failed to compile FullKernel iota rules"
  pure { env, rules, bundle, envC, rulesC }

private def buildWhnfExportRoot (ctx : FullKernelContext) (subcase : String) : Except String (Comb × Comb) := do
  let e ← lookupNamed "whnf subcase" subcase mkCasesWhnf
  let direct :=
    WHNF.whnfWithDelta
      (fun c us => Environment.Env.constValue? (Name := Nat) (Param := Unit) (MetaLevel := Unit)
        (MetaExpr := Unit) ctx.env c us)
      ctx.rules
      20
      e
  let some fuelWhnfC := FullKernelSKY.encodeNatComb? 20
    | throw "failed to encode FullKernel whnf fuel"
  let some eC := FullKernelSKY.compileExprNatUnit? e
    | throw "failed to compile FullKernel expression"
  let some directC := FullKernelSKY.compileExprNatUnit? direct
    | throw "failed to compile FullKernel expected expression"
  let outC :=
    Comb.app
      (Comb.app
        (Comb.app
          (Comb.app ctx.bundle.whnf ctx.envC)
          ctx.rulesC)
        fuelWhnfC)
      eC
  pure (outC, directC)

private def toyRows : Except String (Array TopoRow) := do
  let toyKRoot : Comb := Comb.app (Comb.app .K .K) .S
  let toySRoot : Comb := Comb.app (Comb.app (Comb.app .S .K) .K) .Y
  let toyYRoot : Comb := Comb.app .Y .K
  let toyBranch : Comb := Comb.app (Comb.app .S (Comb.app .Y .K)) (Comb.app .Y .K)
  let toyDiamond : Comb := Comb.app (Comb.app (Comb.app .S (Comb.app .Y .K)) (Comb.app .Y .K)) .K

  let toyKWitness := buildPresentNodeWitness? (buildGraph toyKRoot 4).nodes (combHashString .K)
  let some toySWitness := buildPresentNodeWitness? (buildGraph toySRoot 4).nodes
      (combHashString (Comb.app (Comb.app .K .Y) (Comb.app .K .Y)))
    | throw "toy_s_root_v1: failed to locate expected successor witness"
  let some toyYWitness := buildPresentNodeWitness? (buildGraph toyYRoot 4).nodes
      (combHashString (Comb.app .K (Comb.app .Y .K)))
    | throw "toy_y_root_v1: failed to locate expected successor witness"
  let some toyBranchWitness := buildPresentNodeWitness? (buildGraph toyBranch 4).nodes
      (combHashString (Comb.app (Comb.app .S (Comb.app .K (Comb.app .Y .K))) (Comb.app .Y .K)))
    | throw "toy_branch_pair_v1: failed to locate witness"
  let some toyDiamondWitness := buildPresentNodeWitness? (buildGraph toyDiamond 4).nodes
      (combHashString
        (Comb.app
          (Comb.app (Comb.app .S (Comb.app .K (Comb.app .Y .K))) (Comb.app .K (Comb.app .Y .K)))
          .K))
    | throw "toy_diamond_candidate_v1: failed to locate common-descendant witness"

  let row1 ← mkRow
    "toy_k_root_v1"
    "toy_comb"
    "toy:((K K) S)"
    "sky_witness_only"
    "HeytingLean.CLI.DiffATPTopoCorpusMain"
    ["toy", "root_rule", "K"]
    toyKRoot
    4
    toyKWitness
  let row2 ← mkRow
    "toy_s_root_v1"
    "toy_comb"
    "toy:(((S K) K) Y)"
    "sky_witness_only"
    "HeytingLean.CLI.DiffATPTopoCorpusMain"
    ["toy", "root_rule", "S"]
    toySRoot
    4
    toySWitness
  let row3 ← mkRow
    "toy_y_root_v1"
    "toy_comb"
    "toy:(Y K)"
    "sky_witness_only"
    "HeytingLean.CLI.DiffATPTopoCorpusMain"
    ["toy", "root_rule", "Y"]
    toyYRoot
    4
    toyYWitness
  let row4 ← mkRow
    "toy_branch_pair_v1"
    "toy_comb"
    "toy:((S (Y K)) (Y K))"
    "sky_witness_only"
    "HeytingLean.CLI.DiffATPTopoCorpusMain"
    ["toy", "branch_pair"]
    toyBranch
    4
    toyBranchWitness
  let row5 ← mkRow
    "toy_diamond_candidate_v1"
    "toy_comb"
    "toy:(((S (Y K)) (Y K)) K)"
    "sky_witness_only"
    "HeytingLean.CLI.DiffATPTopoCorpusMain"
    ["toy", "diamond_candidate"]
    toyDiamond
    4
    toyDiamondWitness
  pure #[row1, row2, row3, row4, row5]

private def fullKernelRows : Except String (Array TopoRow) := do
  let ctx ← mkFullKernelContext
  let mkOne (subcase : String) : Except String TopoRow := do
    let (root, direct) ← buildWhnfExportRoot ctx subcase
    let row ← mkRow
      s!"fullkernel_whnf_{subcase}_v1"
      "fullkernel_export"
      s!"full_kernel_sky_demo --case whnf --subcase {subcase} --describe-export"
      "decoded_fragment"
      "HeytingLean.CLI.FullKernelSKYMain"
      ["fullkernel", "whnf", subcase]
      root
      1
      (some (buildExpectedWitness direct))
    let compactNodes :=
      row.nodes.map fun node =>
        { node with termJson := opaqueTermJson node.termHash }
    let compactWitness :=
      some (buildExpectedWitnessWithJson direct (opaqueTermJson (combHashString direct)))
    pure
      { row with
          rootComb := opaqueTermJson row.rootHash
          nodes := compactNodes
          targetWitness? := compactWitness }
  pure #[
    ← mkOne "beta",
    ← mkOne "zeta",
    ← mkOne "iota_zero",
    ← mkOne "iota_succ",
    ← mkOne "delta_only",
    ← mkOne "delta_then_iota",
    ← mkOne "zeta_with_const"
  ]

private def expectedRowIds : Array String :=
  #[
    "toy_k_root_v1",
    "toy_s_root_v1",
    "toy_y_root_v1",
    "toy_branch_pair_v1",
    "toy_diamond_candidate_v1",
    "fullkernel_whnf_beta_v1",
    "fullkernel_whnf_zeta_v1",
    "fullkernel_whnf_iota_zero_v1",
    "fullkernel_whnf_iota_succ_v1",
    "fullkernel_whnf_delta_only_v1",
    "fullkernel_whnf_delta_then_iota_v1",
    "fullkernel_whnf_zeta_with_const_v1"
  ]

private def buildCorpus : Except String TopoCorpusReport := do
  let toy ← toyRows
  let fullKernel ← fullKernelRows
  let rows := toy ++ fullKernel
  let rowIds := rows.map (·.rowId)
  if rowIds != expectedRowIds then
    throw s!"unexpected row ordering: {rowIds}"
  pure
    { schema := "diff_atp_topo_corpus_v1"
      kind := "diff_atp_topo_frozen_corpus"
      honestBoundary :=
        "Lean owns the frozen SKY witness corpus. This corpus is bounded to the depth-indexed 1-skeleton of toy SKY terms plus curated FullKernel WHNF exports, and it does not certify H2, global proof success, or any claim beyond same-row witness/topology analysis."
      rowIds := rowIds
      rows := rows }

private def writeOutput (out? : Option System.FilePath) (payload : String) : IO Unit := do
  match out? with
  | some path => IO.FS.writeFile path payload
  | none => IO.println payload

def main (argv : List String) : IO UInt32 := do
  match parseArgs argv with
  | .error msg =>
      IO.eprintln msg
      pure 1
  | .ok out? =>
      match buildCorpus with
      | .error msg =>
          IO.eprintln s!"[diff_atp_topo_corpus] {msg}"
          pure 1
      | .ok corpus =>
          writeOutput out? ((corpusToJson corpus).pretty)
          pure 0

end HeytingLean.CLI.DiffATPTopoCorpusMain

def main := HeytingLean.CLI.DiffATPTopoCorpusMain.main
