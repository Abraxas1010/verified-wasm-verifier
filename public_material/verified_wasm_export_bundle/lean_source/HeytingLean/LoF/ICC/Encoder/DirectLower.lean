import Lean.Data.Json
import HeytingLean.CLI.SKYStageCore
import HeytingLean.LoF.Combinators.SKYMachineBounded
import HeytingLean.LoF.ICC.Encoder.DeclWalker
import HeytingLean.LoF.LeanKernel.Expression
import HeytingLean.LoF.LeanKernel.Lean4LeanSKY

namespace HeytingLean
namespace LoF
namespace ICC
namespace Encoder

open Lean
open HeytingLean.CLI.SKYStageCore
open HeytingLean.LoF.Combinators
open HeytingLean.LoF.LeanKernel

inductive DirectLoweringStatus where
  | success
  | blocked
  | notApplicable
  deriving DecidableEq, Repr

def DirectLoweringStatus.code : DirectLoweringStatus → String
  | .success => "success"
  | .blocked => "blocked"
  | .notApplicable => "not_applicable"

structure DirectExprLowering where
  projectionsLowered : Bool
  sourceExprNodeCount : Nat
  stagedExprNodeCount : Nat
  stagedTagSet : Array String
  compiledHeapNodes : Nat
  focusNodeTag : String
  erasedUniversePayload : Bool
  erasedExprMetas : Bool
  maxNodes : Nat
  deriving Repr

structure DirectLoweringAttempt where
  status : DirectLoweringStatus
  reason : String
  detail : String
  typeLowering? : Option DirectExprLowering := none
  valueLowering? : Option DirectExprLowering := none
  trustAssumptions : List String := []
  deriving Repr

def leanExprNodeCount : Lean.Expr → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .mvar _ => 1
  | .sort _ => 1
  | .const _ _ => 1
  | .app f a => leanExprNodeCount f + leanExprNodeCount a + 1
  | .lam _ ty body _ => leanExprNodeCount ty + leanExprNodeCount body + 1
  | .forallE _ ty body _ => leanExprNodeCount ty + leanExprNodeCount body + 1
  | .letE _ ty val body _ => leanExprNodeCount ty + leanExprNodeCount val + leanExprNodeCount body + 1
  | .lit _ => 1
  | .mdata _ body => leanExprNodeCount body + 1
  | .proj _ _ body => leanExprNodeCount body + 1

private def focusNodeTag {OracleRef : Type} : SKYMachineBounded.State OracleRef → String
  | s =>
      match s.node? s.focus with
      | some (.combK) => "K"
      | some (.combS) => "S"
      | some (.combY) => "Y"
      | some (.app _ _) => "app"
      | some (.oracle _) => "oracle"
      | none => "missing_focus"

private def insertTag (tag : String) (acc : Std.HashSet String) : Std.HashSet String :=
  acc.insert tag

private def stagedTagSetAux : Expr Nat Unit Unit Unit → Std.HashSet String → Std.HashSet String
  | .bvar _, acc => insertTag "bvar" acc
  | .mvar _, acc => insertTag "mvar" acc
  | .sort _, acc => insertTag "sort" acc
  | .const _ _, acc => insertTag "const" acc
  | .app f a, acc =>
      let acc := insertTag "app" acc
      stagedTagSetAux a (stagedTagSetAux f acc)
  | .lam _ _ ty body, acc =>
      let acc := insertTag "lam" acc
      stagedTagSetAux body (stagedTagSetAux ty acc)
  | .forallE _ _ ty body, acc =>
      let acc := insertTag "forallE" acc
      stagedTagSetAux body (stagedTagSetAux ty acc)
  | .letE _ _ ty val body, acc =>
      let acc := insertTag "letE" acc
      stagedTagSetAux body (stagedTagSetAux val (stagedTagSetAux ty acc))
  | .lit _, acc => insertTag "lit" acc

def stagedTagSet (expr : Expr Nat Unit Unit Unit) : Array String :=
  (stagedTagSetAux expr {}).toList.toArray.qsort (· < ·)

private def loweringTrustAssumptions (stats : DirectExprLowering) : List String :=
  let base := ["direct_decl_body_staging", "staged_kernel_expr_compilation"]
  let base :=
    if stats.projectionsLowered then
      "projection_lowering" :: base
    else
      base
  let base :=
    if stats.erasedUniversePayload then
      "universe_payload_erased" :: base
    else
      base
  let base :=
    if stats.erasedExprMetas then
      "expr_metas_erased" :: base
    else
      base
  base.reverse.eraseDups

private def lowerOneExpr
    (env : Environment)
    (expr : Lean.Expr)
    (maxNodes : Nat) : IO (Except String DirectExprLowering) := do
  let hadProj := containsProj expr
  let loweredResult ← lowerProjExpr env expr
  match loweredResult with
  | .error err => pure (.error err)
  | .ok lowered =>
      match stageExprWithState {} lowered with
      | .error err => pure (.error s!"staging failed: {err}")
      | .ok (staged, st) =>
          match Lean4LeanSKY.Machine.compileExprToState? (maxNodes := maxNodes) staged with
          | none =>
              pure (.error s!"staged Expr compilation exceeded maxNodes={maxNodes}")
          | some compiled =>
              pure (.ok
                { projectionsLowered := hadProj
                  sourceExprNodeCount := leanExprNodeCount expr
                  stagedExprNodeCount := Expr.size staged
                  stagedTagSet := stagedTagSet staged
                  compiledHeapNodes := compiled.nodes.size
                  focusNodeTag := focusNodeTag compiled
                  erasedUniversePayload := st.erasedUniversePayload
                  erasedExprMetas := st.erasedExprMetas
                  maxNodes := maxNodes })

def directLoweringAttempt
    (env : Environment)
    (summary : DeclSummary)
    (ci : ConstantInfo)
    (maxNodes : Nat := 200000) : IO DirectLoweringAttempt := do
  match summary.declKind with
  | "theorem" | "definition" | "opaque" =>
      let typeResult ← lowerOneExpr env ci.type maxNodes
      match typeResult with
      | .error err =>
          pure
            { status := .blocked
              reason := "direct_type_lowering_failed"
              detail := s!"{summary.declName} could not be directly lowered through the staged kernel type path: {err}" }
      | .ok typeLowering =>
          match constantValueExpr? ci with
          | none =>
              pure
                { status := .blocked
                  reason := "direct_value_not_visible"
                  detail := s!"{summary.declName} has a checkable declaration surface but no visible value/proof body for direct staged lowering."
                  typeLowering? := some typeLowering
                  trustAssumptions := loweringTrustAssumptions typeLowering }
          | some value =>
              let valueResult ← lowerOneExpr env value maxNodes
              match valueResult with
              | .error err =>
                  pure
                    { status := .blocked
                      reason := "direct_value_lowering_failed"
                      detail := s!"{summary.declName} lowered its declaration type, but the value/proof body failed direct staged lowering: {err}"
                      typeLowering? := some typeLowering
                      trustAssumptions := loweringTrustAssumptions typeLowering }
              | .ok valueLowering =>
                  pure
                    { status := .success
                      reason := "direct_decl_body_staging"
                      detail := s!"{summary.declName} directly lowers its declaration type and value/proof body into the staged kernel expression plane and compiles to a bounded SKY machine image."
                      typeLowering? := some typeLowering
                      valueLowering? := some valueLowering
                      trustAssumptions := (loweringTrustAssumptions typeLowering ++ loweringTrustAssumptions valueLowering).eraseDups }
  | _ =>
      pure
        { status := .notApplicable
          reason := "direct_lowering_decl_kind_boundary"
          detail := s!"{summary.declName} has declaration kind {summary.declKind}; direct staged lowering currently targets checkable theorem/definition/opaque bodies." }

def directExprLoweringJson (payload : DirectExprLowering) : Json :=
  Json.mkObj
    [ ("projections_lowered", Json.bool payload.projectionsLowered)
    , ("source_expr_node_count", toJson payload.sourceExprNodeCount)
    , ("staged_expr_node_count", toJson payload.stagedExprNodeCount)
    , ("staged_tag_set", Json.arr <| payload.stagedTagSet.map Json.str)
    , ("compiled_heap_nodes", toJson payload.compiledHeapNodes)
    , ("focus_node_tag", Json.str payload.focusNodeTag)
    , ("erased_universe_payload", Json.bool payload.erasedUniversePayload)
    , ("erased_expr_metas", Json.bool payload.erasedExprMetas)
    , ("max_nodes", toJson payload.maxNodes)
    ]

def directLoweringAttemptJson (attempt : DirectLoweringAttempt) : Json :=
  Json.mkObj
    [ ("status", Json.str attempt.status.code)
    , ("reason", Json.str attempt.reason)
    , ("detail", Json.str attempt.detail)
    , ("trust_assumptions", Json.arr <| attempt.trustAssumptions.map Json.str |> List.toArray)
    , ("type_lowering", attempt.typeLowering?.map directExprLoweringJson |>.getD Json.null)
    , ("value_lowering", attempt.valueLowering?.map directExprLoweringJson |>.getD Json.null)
    ]

end Encoder
end ICC
end LoF
end HeytingLean
