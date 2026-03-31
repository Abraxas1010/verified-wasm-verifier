import Lean.Data.Json
import HeytingLean.LoF.LeanKernel.Environment

namespace HeytingLean
namespace LoF
namespace LeanKernel

open Lean

abbrev SLevel := ULevel Nat Nat
abbrev SExpr := Expr Nat Nat Nat Nat
abbrev SConstDecl := Environment.ConstDecl Nat Nat Nat Nat
abbrev SEnv := Environment.Env Nat Nat Nat Nat
abbrev SCtx := Infer.Ctx Nat Nat Nat Nat

structure BundleConst where
  nameId : Nat
  displayName : String
  levelParamIds : List Nat := []
  typeExpr : SExpr
  valueExpr? : Option SExpr := none
  deriving Repr

structure BundleRecursor where
  recursorId : Nat
  displayName : String
  firstMinorIdx : Nat
  majorIdx : Nat
  ctors : List (Inductive.CtorSpec Nat)
  deriving Repr

inductive KernelObligationKind where
  | infer
  | inferSort
  | check
  | whnf
  | defeq
  deriving Repr, DecidableEq

def KernelObligationKind.code : KernelObligationKind → String
  | .infer => "infer"
  | .inferSort => "infer_sort"
  | .check => "check"
  | .whnf => "whnf"
  | .defeq => "defeq"

structure KernelObligation where
  label : String
  kind : KernelObligationKind
  expr : SExpr
  expr2? : Option SExpr := none
  deriving Repr

structure ArbitraryLeanKernelBundle where
  declName : String
  moduleName : String
  declKind : String
  targetType : SExpr
  targetValue? : Option SExpr := none
  localContext : List SExpr := []
  envConsts : List BundleConst := []
  recursors : List BundleRecursor := []
  obligations : List KernelObligation := []
  stagedNameTable : Array String := #[]
  stagedLevelParamTable : Array String := #[]
  stagedLevelMVarTable : Array String := #[]
  stagedExprMVarTable : Array String := #[]
  natConstId : Nat
  stringConstId : Nat
  erasedUniversePayload : Bool := false
  erasedExprMetas : Bool := false
  closureOverflow : Bool := false
  missingDeps : Array String := #[]
  maxConsts : Nat := 0
  deriving Repr

private def binderInfoToString : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

partial def stagedLevelToJson : SLevel → Json
  | .zero => Json.mkObj [("tag", "zero")]
  | .succ u => Json.mkObj [("tag", "succ"), ("level", stagedLevelToJson u)]
  | .max a b => Json.mkObj [("tag", "max"), ("left", stagedLevelToJson a), ("right", stagedLevelToJson b)]
  | .imax a b => Json.mkObj [("tag", "imax"), ("left", stagedLevelToJson a), ("right", stagedLevelToJson b)]
  | .param p => Json.mkObj [("tag", "param"), ("id", toJson p)]
  | .mvar m => Json.mkObj [("tag", "mvar"), ("id", toJson m)]

partial def stagedExprToJson : SExpr → Json
  | .bvar idx => Json.mkObj [("tag", "bvar"), ("idx", toJson idx)]
  | .mvar id => Json.mkObj [("tag", "mvar"), ("id", toJson id)]
  | .sort u => Json.mkObj [("tag", "sort"), ("level", stagedLevelToJson u)]
  | .const id us =>
      Json.mkObj
        [ ("tag", "const")
        , ("id", toJson id)
        , ("levels", Json.arr (us.map stagedLevelToJson).toArray)
        ]
  | .app f a =>
      Json.mkObj [("tag", "app"), ("fn", stagedExprToJson f), ("arg", stagedExprToJson a)]
  | .lam name bi ty body =>
      Json.mkObj
        [ ("tag", "lam")
        , ("name", toJson name)
        , ("binder_info", Json.str (binderInfoToString bi))
        , ("type", stagedExprToJson ty)
        , ("body", stagedExprToJson body)
        ]
  | .forallE name bi ty body =>
      Json.mkObj
        [ ("tag", "forallE")
        , ("name", toJson name)
        , ("binder_info", Json.str (binderInfoToString bi))
        , ("type", stagedExprToJson ty)
        , ("body", stagedExprToJson body)
        ]
  | .letE name _bi ty val body =>
      Json.mkObj
        [ ("tag", "letE")
        , ("name", toJson name)
        , ("type", stagedExprToJson ty)
        , ("value", stagedExprToJson val)
        , ("body", stagedExprToJson body)
        ]
  | .lit (.natVal n) => Json.mkObj [("tag", "lit"), ("kind", "nat"), ("value", toJson n)]
  | .lit (.strVal s) => Json.mkObj [("tag", "lit"), ("kind", "str"), ("value", Json.str s)]

def bundleConstToJson (c : BundleConst) : Json :=
  Json.mkObj
    [ ("name_id", toJson c.nameId)
    , ("display_name", Json.str c.displayName)
    , ("level_param_ids", Json.arr <| c.levelParamIds.map toJson |>.toArray)
    , ("type_expr", stagedExprToJson c.typeExpr)
    , ("value_expr", c.valueExpr?.map stagedExprToJson |>.getD Json.null)
    ]

def bundleRecursorToJson (r : BundleRecursor) : Json :=
  Json.mkObj
    [ ("recursor_id", toJson r.recursorId)
    , ("display_name", Json.str r.displayName)
    , ("first_minor_idx", toJson r.firstMinorIdx)
    , ("major_idx", toJson r.majorIdx)
    , ("ctors",
        Json.arr <| r.ctors.map (fun ctor =>
          Json.mkObj
            [ ("name_id", toJson ctor.name)
            , ("num_params", toJson ctor.numParams)
            , ("num_fields", toJson ctor.numFields)
            , ("recursive_field_positions", Json.arr <| ctor.recursiveFieldPositions.map toJson |>.toArray)
            ]) |>.toArray)
    ]

def obligationToJson (obl : KernelObligation) : Json :=
  Json.mkObj
    [ ("label", Json.str obl.label)
    , ("kind", Json.str obl.kind.code)
    , ("expr", stagedExprToJson obl.expr)
    , ("expr2", obl.expr2?.map stagedExprToJson |>.getD Json.null)
    ]

def bundleToJson (bundle : ArbitraryLeanKernelBundle) : Json :=
  Json.mkObj
    [ ("decl_name", Json.str bundle.declName)
    , ("module_name", Json.str bundle.moduleName)
    , ("decl_kind", Json.str bundle.declKind)
    , ("target_type", stagedExprToJson bundle.targetType)
    , ("target_value", bundle.targetValue?.map stagedExprToJson |>.getD Json.null)
    , ("local_context", Json.arr <| bundle.localContext.map stagedExprToJson |>.toArray)
    , ("env_consts", Json.arr <| bundle.envConsts.map bundleConstToJson |>.toArray)
    , ("recursors", Json.arr <| bundle.recursors.map bundleRecursorToJson |>.toArray)
    , ("obligations", Json.arr <| bundle.obligations.map obligationToJson |>.toArray)
    , ("staged_name_table", Json.arr <| bundle.stagedNameTable.map Json.str)
    , ("staged_level_param_table", Json.arr <| bundle.stagedLevelParamTable.map Json.str)
    , ("staged_level_mvar_table", Json.arr <| bundle.stagedLevelMVarTable.map Json.str)
    , ("staged_expr_mvar_table", Json.arr <| bundle.stagedExprMVarTable.map Json.str)
    , ("nat_const_id", toJson bundle.natConstId)
    , ("string_const_id", toJson bundle.stringConstId)
    , ("erased_universe_payload", Json.bool bundle.erasedUniversePayload)
    , ("erased_expr_metas", Json.bool bundle.erasedExprMetas)
    , ("closure_overflow", Json.bool bundle.closureOverflow)
    , ("missing_deps", Json.arr <| bundle.missingDeps.map Json.str)
    , ("max_consts", toJson bundle.maxConsts)
    ]

/-- Substitute universe-level parameters in a level expression using an
assignment list `[(paramId, replacement), ...]`. -/
def instantiateLevelParams :
    List (Nat × SLevel) → SLevel → SLevel
  | [], u => u
  | (id, v) :: rest, .param p => if p == id then v else instantiateLevelParams rest (.param p)
  | assignments, .succ u => .succ (instantiateLevelParams assignments u)
  | assignments, .max a b => .max (instantiateLevelParams assignments a) (instantiateLevelParams assignments b)
  | assignments, .imax a b => .imax (instantiateLevelParams assignments a) (instantiateLevelParams assignments b)
  | _, .zero => .zero
  | _, .mvar m => .mvar m

/-- Substitute universe-level parameters in an expression using an assignment list. -/
def instantiateExprLevelParams :
    List (Nat × SLevel) → SExpr → SExpr
  | _, .bvar i => .bvar i
  | _, .mvar m => .mvar m
  | assignments, .sort u => .sort (instantiateLevelParams assignments u)
  | assignments, .const n us => .const n (us.map (instantiateLevelParams assignments))
  | assignments, .app f a =>
      .app (instantiateExprLevelParams assignments f) (instantiateExprLevelParams assignments a)
  | assignments, .lam n bi ty body =>
      .lam n bi (instantiateExprLevelParams assignments ty) (instantiateExprLevelParams assignments body)
  | assignments, .forallE n bi ty body =>
      .forallE n bi (instantiateExprLevelParams assignments ty) (instantiateExprLevelParams assignments body)
  | assignments, .letE n bi ty val body =>
      .letE n bi
        (instantiateExprLevelParams assignments ty)
        (instantiateExprLevelParams assignments val)
        (instantiateExprLevelParams assignments body)
  | _, .lit l => .lit l

/-- Instantiate an expression's universe-level parameters with the given levels. -/
def instantiateWithLevels (levelParamIds : List Nat) (us : List SLevel) (expr : SExpr) : SExpr :=
  instantiateExprLevelParams (levelParamIds.zip us) expr

def bundleToEnv (bundle : ArbitraryLeanKernelBundle) : SEnv :=
  let consts :=
    bundle.envConsts.map fun c =>
      match c.valueExpr? with
      | some val =>
          { name := c.nameId
            type := fun us => instantiateWithLevels c.levelParamIds us c.typeExpr
            value? := some (fun us => instantiateWithLevels c.levelParamIds us val) }
      | none =>
          { name := c.nameId
            type := fun us => instantiateWithLevels c.levelParamIds us c.typeExpr
            value? := none }
  let casesOnSpecs :=
    bundle.recursors.map fun r =>
      { recursor := r.recursorId
        firstMinorIdx := r.firstMinorIdx
        majorIdx := r.majorIdx
        ctors := r.ctors }
  { beqName := fun a b => a == b
    consts := consts
    casesOnSpecs := casesOnSpecs
    mvarType? := fun _ => none
    litType? := fun lit =>
      match lit with
      | .natVal _ => some (.const bundle.natConstId [])
      | .strVal _ => some (.const bundle.stringConstId []) }

end LeanKernel
end LoF
end HeytingLean
