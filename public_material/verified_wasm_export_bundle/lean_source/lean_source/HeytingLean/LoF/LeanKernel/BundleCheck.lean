import Lean.Data.Json
import HeytingLean.LoF.LeanKernel.BundleSchema
import HeytingLean.LoF.LeanKernel.DefEq
import HeytingLean.LoF.LeanKernel.Infer
import HeytingLean.LoF.LeanKernel.WHNF

namespace HeytingLean
namespace LoF
namespace LeanKernel

open Lean

inductive BundleCheckStatus where
  | success
  | blocked
  | unsupported
  deriving Repr, DecidableEq

def BundleCheckStatus.code : BundleCheckStatus → String
  | .success => "success"
  | .blocked => "blocked"
  | .unsupported => "unsupported"

structure ObligationResult where
  label : String
  kind : String
  status : BundleCheckStatus
  detail : Json

private def ctxOfLocalContext (xs : List SExpr) : SCtx :=
  xs.foldl (init := Infer.Ctx.empty) fun ctx ty => ctx.extend ty

private def exprBrief (e : SExpr) (limit : Nat := 1200) : String :=
  let s := reprStr e
  if s.length <= limit then s else s.take limit ++ "..."

mutual
  private def defEqDiagnostic
      (cfg : Infer.Config Nat Nat Nat Nat) :
      Nat → SExpr → SExpr → String
    | 0, e1, e2 =>
        s!"defeq_fuel_exhausted[lhs={exprBrief e1 300}, rhs={exprBrief e2 300}]"
    | fuel + 1, e1, e2 =>
        if DefEq.isDefEqWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) e1 e2 then
          "defeq_ok"
        else
          let w1 := WHNF.whnfWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) e1
          let w2 := WHNF.whnfWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) e2
          match w1, w2 with
          | .app f a, .app g b =>
              if !(DefEq.isDefEqWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) f g) then
                s!"defeq_fn[{defEqDiagnostic cfg fuel f g}]"
              else
                s!"defeq_arg[{defEqDiagnostic cfg fuel a b}]"
          | .lam _ _ ty body, .lam _ _ ty' body' =>
              if !(DefEq.isDefEqWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) ty ty') then
                s!"defeq_lam_type[{defEqDiagnostic cfg fuel ty ty'}]"
              else
                s!"defeq_lam_body[{defEqDiagnostic cfg fuel body body'}]"
          | .forallE _ _ ty body, .forallE _ _ ty' body' =>
              if !(DefEq.isDefEqWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) ty ty') then
                s!"defeq_forall_type[{defEqDiagnostic cfg fuel ty ty'}]"
              else
                s!"defeq_forall_body[{defEqDiagnostic cfg fuel body body'}]"
          | .const c us, .const d vs =>
              s!"defeq_const_mismatch[lhs={c}:{reprStr us}, rhs={d}:{reprStr vs}]"
          | .sort u, .sort v =>
              s!"defeq_sort_mismatch[lhs={reprStr u}, rhs={reprStr v}]"
          | _, _ =>
              s!"defeq_shape_mismatch[lhs={exprBrief w1 400}, rhs={exprBrief w2 400}]"

  private def inferDiagnostic
      (cfg : Infer.Config Nat Nat Nat Nat) :
      Nat → SCtx → SExpr → Except String SExpr
    | 0, _, _ => .error "fuel_exhausted"
    | fuel + 1, ctx, e =>
        match e with
        | .bvar i =>
            match ctx.bvarType? i with
            | some ty => .ok ty
            | none => .error s!"bvar_out_of_scope[{i}]"
        | .mvar m =>
            match cfg.mvarType? m with
            | some ty => .ok ty
            | none => .error s!"mvar_type_missing[{m}]"
        | .lit l =>
            match cfg.litType? l with
            | some ty => .ok ty
            | none => .error s!"lit_type_missing[{reprStr l}]"
        | .sort u => .ok (.sort (.succ u))
        | .const c us =>
            match cfg.constType? c us with
            | some ty => .ok ty
            | none => .error s!"const_type_missing[{c}:{reprStr us}]"
        | .app f a =>
            match inferDiagnostic cfg fuel ctx f with
            | .error err => .error s!"infer_fn[{err}]"
            | .ok tf =>
                let tfWhnf := WHNF.whnfWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) tf
                match tfWhnf with
                | .forallE _ _ dom body =>
                    match inferDiagnostic cfg fuel ctx a with
                    | .error err => .error s!"infer_arg[{err}]"
                    | .ok ta =>
                        if DefEq.isDefEqWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) ta dom then
                          .ok (Expr.instantiate1 a body)
                        else
                          .error s!"app_arg_type_mismatch[{defEqDiagnostic cfg fuel ta dom}]"
                | _ =>
                    .error s!"app_fn_not_forall[{exprBrief tfWhnf 300}]"
        | .lam bn bi ty body =>
            match inferSortDiagnostic cfg fuel ctx ty with
            | .error err => .error s!"lam_domain_not_sort[{err}]"
            | .ok _ =>
                match inferDiagnostic cfg fuel (ctx.extend ty) body with
                | .ok bodyTy => .ok (.forallE bn bi ty bodyTy)
                | .error err => .error s!"lam_body[{err}]"
        | .forallE _ _ ty body =>
            match inferSortDiagnostic cfg fuel ctx ty with
            | .error err => .error s!"forall_domain_not_sort[{err}]"
            | .ok u =>
                match inferSortDiagnostic cfg fuel (ctx.extend ty) body with
                | .ok v => .ok (.sort (.imax u v))
                | .error err => .error s!"forall_body_not_sort[{err}]"
        | .letE _ _ ty val body =>
            match inferSortDiagnostic cfg fuel ctx ty with
            | .error err => .error s!"let_type_not_sort[{err}]"
            | .ok _ =>
                match inferDiagnostic cfg fuel ctx val with
                | .error err => .error s!"let_value[{err}]"
                | .ok tVal =>
                    if DefEq.isDefEqWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) tVal ty then
                      match inferDiagnostic cfg fuel (ctx.extend ty) body with
                      | .ok bodyTy => .ok (Expr.instantiate1 val bodyTy)
                      | .error err => .error s!"let_body[{err}]"
                    else
                      .error s!"let_value_type_mismatch[{defEqDiagnostic cfg fuel tVal ty}]"

  private def inferSortDiagnostic
      (cfg : Infer.Config Nat Nat Nat Nat) :
      Nat → SCtx → SExpr → Except String SLevel
    | 0, _, _ => .error "fuel_exhausted"
    | fuel + 1, ctx, e =>
        match inferDiagnostic cfg fuel ctx e with
        | .error err => .error err
        | .ok ty =>
            match WHNF.whnfWithDelta cfg.constValue? cfg.iotaRules (fuel + 1) ty with
            | .sort u => .ok u
            | tyWhnf => .error s!"not_sort[{exprBrief tyWhnf 300}]"
end

def checkObligation
    (bundle : ArbitraryLeanKernelBundle)
    (obl : KernelObligation)
    (fuel : Nat := 256) : ObligationResult :=
  let env := bundleToEnv bundle
  let cfg := env.toInferConfig
  let ctx := ctxOfLocalContext bundle.localContext
  match obl.kind with
  | .infer =>
      match inferDiagnostic cfg fuel ctx obl.expr with
      | .ok inferredType =>
          let inferredWhnf := WHNF.whnfWithDelta cfg.constValue? cfg.iotaRules fuel inferredType
          { label := obl.label
            kind := obl.kind.code
            status := .success
            detail := Json.mkObj
              [ ("inferred_type", stagedExprToJson inferredType)
              , ("inferred_type_whnf", stagedExprToJson inferredWhnf)
              ] }
      | .error err =>
          { label := obl.label
            kind := obl.kind.code
            status := .blocked
            detail := Json.mkObj [("diagnostic", Json.str err)] }
  | .inferSort =>
      match inferSortDiagnostic cfg fuel ctx obl.expr with
      | .ok level =>
          { label := obl.label
            kind := obl.kind.code
            status := .success
            detail := Json.mkObj [("sort_level", stagedLevelToJson level)] }
      | .error err =>
          { label := obl.label
            kind := obl.kind.code
            status := .blocked
            detail := Json.mkObj [("diagnostic", Json.str err)] }
  | .check =>
      match obl.expr2? with
      | none =>
          { label := obl.label
            kind := obl.kind.code
            status := .unsupported
            detail := Json.mkObj [("diagnostic", Json.str "missing_target_type")] }
      | some expectedType =>
          match inferDiagnostic cfg fuel ctx obl.expr with
          | .error err =>
              { label := obl.label
                kind := obl.kind.code
                status := .blocked
                detail := Json.mkObj [("diagnostic", Json.str err)] }
          | .ok inferredType =>
              let inferredWhnf := WHNF.whnfWithDelta cfg.constValue? cfg.iotaRules fuel inferredType
              let targetWhnf := WHNF.whnfWithDelta cfg.constValue? cfg.iotaRules fuel expectedType
              let ok := DefEq.isDefEqWithDelta cfg.constValue? cfg.iotaRules fuel inferredType expectedType
              if ok then
                { label := obl.label
                  kind := obl.kind.code
                  status := .success
                  detail := Json.mkObj
                    [ ("inferred_type", stagedExprToJson inferredType)
                    , ("inferred_type_whnf", stagedExprToJson inferredWhnf)
                    , ("target_type_whnf", stagedExprToJson targetWhnf)
                    ] }
              else
                { label := obl.label
                  kind := obl.kind.code
                  status := .blocked
                  detail := Json.mkObj
                    [ ("diagnostic", Json.str (defEqDiagnostic cfg fuel inferredType expectedType))
                    , ("inferred_type", stagedExprToJson inferredType)
                    , ("inferred_type_whnf", stagedExprToJson inferredWhnf)
                    , ("target_type_whnf", stagedExprToJson targetWhnf)
                    ] }
  | .whnf =>
      let out := WHNF.whnfWithDelta cfg.constValue? cfg.iotaRules fuel obl.expr
      { label := obl.label
        kind := obl.kind.code
        status := .success
        detail := Json.mkObj [("whnf", stagedExprToJson out)] }
  | .defeq =>
      match obl.expr2? with
      | none =>
          { label := obl.label
            kind := obl.kind.code
            status := .unsupported
            detail := Json.mkObj [("diagnostic", Json.str "missing_rhs")] }
      | some rhs =>
          let ok := DefEq.isDefEqWithDelta cfg.constValue? cfg.iotaRules fuel obl.expr rhs
          if ok then
            { label := obl.label
              kind := obl.kind.code
              status := .success
              detail := Json.mkObj [("parity", Json.str "defeq_ok")] }
          else
            { label := obl.label
              kind := obl.kind.code
              status := .blocked
              detail := Json.mkObj [("diagnostic", Json.str (defEqDiagnostic cfg fuel obl.expr rhs))] }

def checkBundle
    (bundle : ArbitraryLeanKernelBundle)
    (fuel : Nat := 256) : List ObligationResult :=
  bundle.obligations.map (fun obl => checkObligation bundle obl fuel)

def obligationResultToJson (result : ObligationResult) : Json :=
  Json.mkObj
    [ ("label", Json.str result.label)
    , ("kind", Json.str result.kind)
    , ("status", Json.str result.status.code)
    , ("detail", result.detail)
    ]

end LeanKernel
end LoF
end HeytingLean
