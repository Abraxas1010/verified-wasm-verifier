import Lean.Data.Json
import HeytingLean.LoF.LeanKernel.BundleCheck
import HeytingLean.LoF.LeanKernel.BundleSchema

namespace HeytingLean
namespace LoF
namespace LeanKernel

/-!
# KernelMapping

Lean-owned canonical projection from exported kernel bundles into stable
obligation rows. This is the first semantic boundary in the widening pipeline.
-/

open Lean

structure CanonicalObligationRow where
  rowId : String
  declName : String
  moduleName : String
  declKind : String
  obligationLabel : String
  kind : KernelObligationKind
  primaryExpr : SExpr
  secondaryExpr? : Option SExpr := none
  targetType : SExpr
  targetValue? : Option SExpr := none
  localContext : List SExpr := []
  deriving Repr, DecidableEq

def canonicalRowId (bundle : ArbitraryLeanKernelBundle) (obligation : KernelObligation) : String :=
  String.intercalate "::"
    [ bundle.moduleName
    , bundle.declName
    , obligation.label
    , obligation.kind.code
    ]

def obligationToCanonicalRow
    (bundle : ArbitraryLeanKernelBundle)
    (obligation : KernelObligation) : CanonicalObligationRow :=
  { rowId := canonicalRowId bundle obligation
    declName := bundle.declName
    moduleName := bundle.moduleName
    declKind := bundle.declKind
    obligationLabel := obligation.label
    kind := obligation.kind
    primaryExpr := obligation.expr
    secondaryExpr? := obligation.expr2?
    targetType := bundle.targetType
    targetValue? := bundle.targetValue?
    localContext := bundle.localContext }

def bundleToCanonicalRows (bundle : ArbitraryLeanKernelBundle) : List CanonicalObligationRow :=
  bundle.obligations.map (obligationToCanonicalRow bundle)

private def parseBinderInfo (raw : String) : Except String BinderInfo :=
  match raw with
  | "default" => .ok .default
  | "implicit" => .ok .implicit
  | "strictImplicit" => .ok .strictImplicit
  | "instImplicit" => .ok .instImplicit
  | other => .error s!"unknown binder_info: {other}"

private partial def stagedLevelFromJson (j : Json) : Except String SLevel := do
  let tag ← j.getObjValAs? String "tag"
  match tag with
  | "zero" => .ok .zero
  | "succ" =>
      let level ← j.getObjVal? "level"
      .ok (.succ (← stagedLevelFromJson level))
  | "max" =>
      let left ← j.getObjVal? "left"
      let right ← j.getObjVal? "right"
      .ok (.max (← stagedLevelFromJson left) (← stagedLevelFromJson right))
  | "imax" =>
      let left ← j.getObjVal? "left"
      let right ← j.getObjVal? "right"
      .ok (.imax (← stagedLevelFromJson left) (← stagedLevelFromJson right))
  | "param" =>
      let id ← j.getObjValAs? Nat "id"
      .ok (.param id)
  | "mvar" =>
      let id ← j.getObjValAs? Nat "id"
      .ok (.mvar id)
  | other => .error s!"unknown staged level tag: {other}"

private partial def stagedExprFromJson (j : Json) : Except String SExpr := do
  let tag ← j.getObjValAs? String "tag"
  match tag with
  | "bvar" =>
      let idx ← j.getObjValAs? Nat "idx"
      .ok (.bvar idx)
  | "mvar" =>
      let id ← j.getObjValAs? Nat "id"
      .ok (.mvar id)
  | "sort" =>
      let level ← j.getObjVal? "level"
      .ok (.sort (← stagedLevelFromJson level))
  | "const" =>
      let id ← j.getObjValAs? Nat "id"
      let levelsJson ← j.getObjValAs? (Array Json) "levels"
      .ok (.const id (← levelsJson.toList.mapM stagedLevelFromJson))
  | "app" =>
      let fn ← j.getObjVal? "fn"
      let arg ← j.getObjVal? "arg"
      .ok (.app (← stagedExprFromJson fn) (← stagedExprFromJson arg))
  | "lam" =>
      let name ← j.getObjValAs? Nat "name"
      let binderInfoRaw ← j.getObjValAs? String "binder_info"
      let ty ← j.getObjVal? "type"
      let body ← j.getObjVal? "body"
      .ok (.lam name (← parseBinderInfo binderInfoRaw) (← stagedExprFromJson ty) (← stagedExprFromJson body))
  | "forallE" =>
      let name ← j.getObjValAs? Nat "name"
      let binderInfoRaw ← j.getObjValAs? String "binder_info"
      let ty ← j.getObjVal? "type"
      let body ← j.getObjVal? "body"
      .ok (.forallE name (← parseBinderInfo binderInfoRaw) (← stagedExprFromJson ty) (← stagedExprFromJson body))
  | "letE" =>
      let name ← j.getObjValAs? Nat "name"
      let ty ← j.getObjVal? "type"
      let value ← j.getObjVal? "value"
      let body ← j.getObjVal? "body"
      .ok (.letE name .default (← stagedExprFromJson ty) (← stagedExprFromJson value) (← stagedExprFromJson body))
  | "lit" =>
      let kind ← j.getObjValAs? String "kind"
      match kind with
      | "nat" =>
          let value ← j.getObjValAs? Nat "value"
          .ok (.lit (.natVal value))
      | "str" =>
          let value ← j.getObjValAs? String "value"
          .ok (.lit (.strVal value))
      | other => .error s!"unknown literal kind: {other}"
  | other => .error s!"unknown staged expr tag: {other}"

private def inferredTypeFromCheckResult? (result : ObligationResult) : Option SExpr :=
  if result.kind = KernelObligationKind.check.code && result.status = .success then
    match result.detail.getObjVal? "inferred_type" with
    | .ok inferredTypeJson =>
        match stagedExprFromJson inferredTypeJson with
        | .ok inferredType => some inferredType
        | .error _ => none
    | .error _ => none
  else
    none

private def inferredTypeWhnfFromCheckResult? (result : ObligationResult) : Option SExpr :=
  if result.kind = KernelObligationKind.check.code && result.status = .success then
    match result.detail.getObjVal? "inferred_type_whnf" with
    | .ok inferredTypeJson =>
        match stagedExprFromJson inferredTypeJson with
        | .ok inferredType => some inferredType
        | .error _ => none
    | .error _ => none
  else
    none

private def targetTypeWhnfFromCheckResult? (result : ObligationResult) : Option SExpr :=
  if result.kind = KernelObligationKind.check.code && result.status = .success then
    match result.detail.getObjVal? "target_type_whnf" with
    | .ok targetTypeJson =>
        match stagedExprFromJson targetTypeJson with
        | .ok targetType => some targetType
        | .error _ => none
    | .error _ => none
  else
    none

private def eqPayload? : SExpr → Option (SExpr × SExpr × SExpr)
  | .app (.app (.app (.const eqId _) typeExpr) lhsExpr) rhsExpr =>
      if eqId = 1 then
        some (typeExpr, lhsExpr, rhsExpr)
      else
        none
  | _ => none

private def reflEqPayloadWitness?
    (inferredTypeWhnf expectedTypeWhnf : SExpr) : Option (SExpr × SExpr × SExpr) :=
  match eqPayload? inferredTypeWhnf, eqPayload? expectedTypeWhnf with
  | some (inferTy, inferLhs, inferRhs), some (declTy, declLhs, declRhs) =>
      if inferTy = declTy && inferLhs = declLhs && inferRhs = inferLhs then
        some (declTy, inferRhs, declRhs)
      else
        none
  | _, _ => none

private def derivedDefEqLabel (label : String) : String :=
  if label.endsWith "_check" then
    label.dropRight 6 ++ "_defeq_inferred_declared"
  else
    label ++ "_defeq_inferred_declared"

def derivedDefEqRow?
    (bundle : ArbitraryLeanKernelBundle)
    (obligation : KernelObligation)
    (result : ObligationResult) : Option CanonicalObligationRow := do
  let inferredType ← inferredTypeFromCheckResult? result
  let expectedType ← obligation.expr2?
  let inferredTypeWhnf := inferredTypeWhnfFromCheckResult? result
  let expectedTypeWhnf := targetTypeWhnfFromCheckResult? result
  let (primaryExpr, secondaryExpr?) :=
    match inferredTypeWhnf, expectedTypeWhnf with
    | some inferredWhnf, some expectedWhnf =>
        match reflEqPayloadWitness? inferredWhnf expectedWhnf with
        | some (_, lhsWitness, rhsWitness) => (lhsWitness, some rhsWitness)
        | none => (inferredType, some expectedType)
    | _, _ => (inferredType, some expectedType)
  let derivedObligation : KernelObligation :=
    { label := derivedDefEqLabel obligation.label
      kind := .defeq
      expr := primaryExpr
      expr2? := secondaryExpr? }
  some (obligationToCanonicalRow bundle derivedObligation)

def bundleToCanonicalRowsWithResults
    (bundle : ArbitraryLeanKernelBundle)
    (results : List ObligationResult) : List CanonicalObligationRow :=
  let derivedRows :=
    (List.zip bundle.obligations results).filterMap (fun (obligation, result) =>
      derivedDefEqRow? bundle obligation result)
  bundleToCanonicalRows bundle ++ derivedRows

@[simp] theorem obligationToCanonicalRow_rowId
    (bundle : ArbitraryLeanKernelBundle)
    (obligation : KernelObligation) :
    (obligationToCanonicalRow bundle obligation).rowId = canonicalRowId bundle obligation := rfl

@[simp] theorem obligationToCanonicalRow_declName
    (bundle : ArbitraryLeanKernelBundle)
    (obligation : KernelObligation) :
    (obligationToCanonicalRow bundle obligation).declName = bundle.declName := rfl

@[simp] theorem obligationToCanonicalRow_moduleName
    (bundle : ArbitraryLeanKernelBundle)
    (obligation : KernelObligation) :
    (obligationToCanonicalRow bundle obligation).moduleName = bundle.moduleName := rfl

@[simp] theorem obligationToCanonicalRow_declKind
    (bundle : ArbitraryLeanKernelBundle)
    (obligation : KernelObligation) :
    (obligationToCanonicalRow bundle obligation).declKind = bundle.declKind := rfl

@[simp] theorem obligationToCanonicalRow_label
    (bundle : ArbitraryLeanKernelBundle)
    (obligation : KernelObligation) :
    (obligationToCanonicalRow bundle obligation).obligationLabel = obligation.label := rfl

@[simp] theorem obligationToCanonicalRow_kind
    (bundle : ArbitraryLeanKernelBundle)
    (obligation : KernelObligation) :
    (obligationToCanonicalRow bundle obligation).kind = obligation.kind := rfl

@[simp] theorem obligationToCanonicalRow_primaryExpr
    (bundle : ArbitraryLeanKernelBundle)
    (obligation : KernelObligation) :
    (obligationToCanonicalRow bundle obligation).primaryExpr = obligation.expr := rfl

@[simp] theorem obligationToCanonicalRow_secondaryExpr
    (bundle : ArbitraryLeanKernelBundle)
    (obligation : KernelObligation) :
    (obligationToCanonicalRow bundle obligation).secondaryExpr? = obligation.expr2? := rfl

@[simp] theorem obligationToCanonicalRow_targetType
    (bundle : ArbitraryLeanKernelBundle)
    (obligation : KernelObligation) :
    (obligationToCanonicalRow bundle obligation).targetType = bundle.targetType := rfl

@[simp] theorem obligationToCanonicalRow_targetValue
    (bundle : ArbitraryLeanKernelBundle)
    (obligation : KernelObligation) :
    (obligationToCanonicalRow bundle obligation).targetValue? = bundle.targetValue? := rfl

@[simp] theorem obligationToCanonicalRow_localContext
    (bundle : ArbitraryLeanKernelBundle)
    (obligation : KernelObligation) :
    (obligationToCanonicalRow bundle obligation).localContext = bundle.localContext := rfl

@[simp] theorem bundleToCanonicalRows_length
    (bundle : ArbitraryLeanKernelBundle) :
    (bundleToCanonicalRows bundle).length = bundle.obligations.length := by
  simp [bundleToCanonicalRows]

@[simp] theorem bundleToCanonicalRows_nil_iff
    (bundle : ArbitraryLeanKernelBundle) :
    bundleToCanonicalRows bundle = [] ↔ bundle.obligations = [] := by
  simp [bundleToCanonicalRows]

theorem bundleToCanonicalRowsWithResults_length_ge
    (bundle : ArbitraryLeanKernelBundle)
    (results : List ObligationResult) :
    bundle.obligations.length ≤ (bundleToCanonicalRowsWithResults bundle results).length := by
  simp [bundleToCanonicalRowsWithResults]

end LeanKernel
end LoF
end HeytingLean
