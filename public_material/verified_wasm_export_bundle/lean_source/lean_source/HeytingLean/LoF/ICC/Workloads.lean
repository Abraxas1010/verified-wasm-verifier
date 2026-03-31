import Lean.Data.Json
import HeytingLean.LoF.ICC.Encodings
import HeytingLean.LoF.ICC.Reduction
import HeytingLean.Bridge.INet.ICCLowering

namespace HeytingLean
namespace LoF
namespace ICC

open Lean
open HeytingLean.Bridge.INet.ICC

structure WorkloadCase where
  name : String
  term : Term
  expectedClass : RewriteClass
  tags : List String := []

def sampleTerm : Term :=
  .ann (embedLegacy (.app (.app .K .S) .Y)) (Arr Set Set)

def workloadCases : List WorkloadCase :=
  [ { name := "app_lam_id_k"
      term := .app (.lam (.var 0)) kTerm
      expectedClass := .appLam
      tags := ["rewrite", "yfree_positive"] }
  , { name := "app_lam_then_ann_bridge"
      term := .app (.lam (.ann (.var 0) (.bridge (.var 1)))) kTerm
      expectedClass := .appLam
      tags := ["rewrite", "multi_step", "yfree_positive"] }
  , { name := "app_lam_then_ann_lam"
      term := .app (.lam (.ann (.var 0) (.lam (.var 1)))) kTerm
      expectedClass := .appLam
      tags := ["rewrite", "multi_step", "yfree_positive"] }
  , { name := "app_bridge_id_k"
      term := .app (.bridge (.var 0)) kTerm
      expectedClass := .appBridge
      tags := ["rewrite", "yfree_positive"] }
  , { name := "ann_lam_k_id"
      term := .ann kTerm (.lam (.var 0))
      expectedClass := .annLam
      tags := ["rewrite", "yfree_positive"] }
  , { name := "ann_bridge_k_id"
      term := .ann kTerm (.bridge (.var 0))
      expectedClass := .annBridge
      tags := ["rewrite", "yfree_positive"] }
  , { name := "ann_bridge_then_app_lam"
      term := .ann (.app (.lam (.var 0)) kTerm) (.bridge (.var 0))
      expectedClass := .annBridge
      tags := ["rewrite", "multi_step", "yfree_positive"] }
  , { name := "ann_bridge_then_app_bridge"
      term := .ann (.app (.bridge (.var 0)) kTerm) (.bridge (.var 0))
      expectedClass := .annBridge
      tags := ["rewrite", "multi_step", "yfree_positive"] }
  , { name := "ann_unsupported_app"
      term := .ann kTerm (.app kTerm kTerm)
      expectedClass := .unsupported
      tags := ["unsupported", "yfree_positive"] }
  , { name := "normal_k"
      term := kTerm
      expectedClass := .none
      tags := ["normal_form", "yfree_positive"] }
  , { name := "legacy_y_sample"
      term := sampleTerm
      expectedClass := .unsupported
      tags := ["legacy_y_negative"] }
  ]

def termJson : Term → Json
  | .var idx =>
      Json.mkObj [("tag", Json.str "var"), ("value", Json.num idx)]
  | .lam body =>
      Json.mkObj [("tag", Json.str "lam"), ("value", termJson body)]
  | .app fn arg =>
      Json.mkObj [("tag", Json.str "app"), ("value", Json.arr #[termJson fn, termJson arg])]
  | .bridge body =>
      Json.mkObj [("tag", Json.str "bridge"), ("value", termJson body)]
  | .ann val typ =>
      Json.mkObj [("tag", Json.str "ann"), ("value", Json.arr #[termJson val, termJson typ])]

def rewriteClassJson (cls : RewriteClass) : Json :=
  Json.str cls.toString

private def rootSiteWire? (net : ICCNet) (root : Port) : Option Wire := do
  if root.role != .principal then
    none
  else
    let node ← net.node? root.agent
    let role ←
      match node.kind with
      | .app => some .aux1
      | .ann => some .aux2
      | _ => none
    let sitePort : Port := { agent := root.agent, role := role }
    net.wires.find? (fun wire => wire.lhs = sitePort || wire.rhs = sitePort)

private partial def runtimePrimaryClassFromPort (net : ICCNet) (root : Port) : RewriteClass :=
  if root.role != .principal then
    .none
  else
    match net.node? root.agent with
    | none => .none
    | some node =>
        match node.kind with
        | .app | .ann =>
            match rootSiteWire? net root with
            | some wire =>
                let cls := net.classifyWire wire
                if cls != .none then
                  cls
                else
                  let lhs := node.captures[0]?.map (runtimePrimaryClassFromPort net) |>.getD .none
                  if lhs != .none then
                    lhs
                  else
                    node.captures[1]?.map (runtimePrimaryClassFromPort net) |>.getD .none
            | none =>
                let lhs := node.captures[0]?.map (runtimePrimaryClassFromPort net) |>.getD .none
                if lhs != .none then
                  lhs
                else
                  node.captures[1]?.map (runtimePrimaryClassFromPort net) |>.getD .none
        | .var | .lam | .bridge | .dup | .era => .none

private def runtimePrimaryClass (net : ICCNet) : RewriteClass :=
  runtimePrimaryClassFromPort net net.root

private def runtimeStepTermJson (primary : RewriteClass) (t : Term) : Json :=
  match primary with
  | .appLam | .appBridge | .annLam | .annBridge =>
      match step? t with
      | some u => termJson u
      | none => Json.null
  | .unsupported | .none => Json.null

private def runtimeReduceTermJson (primary : RewriteClass) (fuel : Nat) (t : Term) : Json :=
  match primary with
  | .appLam | .appBridge | .annLam | .annBridge => termJson (reduceFuel fuel t)
  | .unsupported | .none => termJson t

private partial def runtimeClassTrace (fuel : Nat) (t : Term) : List RewriteClass :=
  let net := lower t
  let primaryClass := runtimePrimaryClass net
  match fuel, primaryClass with
  | _, .unsupported | _, .none => [primaryClass]
  | 0, _ => [primaryClass]
  | fuel + 1, _ =>
      match step? t with
      | some u => primaryClass :: runtimeClassTrace fuel u
      | none => [primaryClass]

private partial def runtimeTermTrace (fuel : Nat) (t : Term) : List Term :=
  let net := lower t
  let primaryClass := runtimePrimaryClass net
  match fuel, primaryClass with
  | _, .unsupported | _, .none => [t]
  | 0, _ => [t]
  | fuel + 1, _ =>
      match step? t with
      | some u => t :: runtimeTermTrace fuel u
      | none => [t]

private def caseReport (fuel : Nat) (row : WorkloadCase) : Json :=
  let net := lower row.term
  let activeClasses := net.activePairClasses
  let primaryClass := runtimePrimaryClass net
  let classTrace := runtimeClassTrace fuel row.term
  let termTrace := runtimeTermTrace fuel row.term
  let stepTerm :=
    match termTrace.drop 1 |>.head? with
    | some u => termJson u
    | none => Json.null
  let reduceTerm :=
    match termTrace.reverse.head? with
    | some u => termJson u
    | none => termJson row.term
  Json.mkObj
    [ ("name", Json.str row.name)
    , ("expected_class", rewriteClassJson row.expectedClass)
    , ("tags", Json.arr <| row.tags.map Json.str |>.toArray)
    , ("term", termJson row.term)
    , ("term_size", Json.num row.term.size)
    , ("primary_class", rewriteClassJson primaryClass)
    , ("class_trace", Json.arr <| classTrace.map rewriteClassJson |>.toArray)
    , ("term_trace", Json.arr <| termTrace.map termJson |>.toArray)
    , ("step_count", Json.num termTrace.tail.length)
    , ("step_term", stepTerm)
    , ("reduce_term", reduceTerm)
    , ("y_free_input", Json.bool (isYFree row.term))
    , ("check_y_free", Json.bool (checkYFree fuel row.term))
    , ("net", emitJson net)
    , ("active_pair_classes", Json.arr <| activeClasses.map rewriteClassJson |>.toArray)
    ]

def workloadReportJson (fuel : Nat := 8) : Json :=
  Json.mkObj
    [ ("schema", Json.str "icc_workload_v1")
    , ("fuel", Json.num fuel)
    , ("cases", Json.arr <| workloadCases.map (caseReport fuel) |>.toArray)
    ]

end ICC
end LoF
end HeytingLean
