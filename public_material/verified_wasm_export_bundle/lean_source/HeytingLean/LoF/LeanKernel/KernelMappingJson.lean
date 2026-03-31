import Lean.Data.Json
import HeytingLean.LoF.LeanKernel.KernelOverlay

namespace HeytingLean
namespace LoF
namespace LeanKernel

open Lean
open HeytingLean.LeanCP

private def jsonStringArray (xs : List String) : Json :=
  Json.arr <| xs.toArray.map Json.str

private def jsonExprArray (xs : List SExpr) : Json :=
  Json.arr <| xs.toArray.map stagedExprToJson

private def jsonExprOption (x : Option SExpr) : Json :=
  x.map stagedExprToJson |>.getD Json.null

def canonicalObligationRowToJson (row : CanonicalObligationRow) : Json :=
  Json.mkObj
    [ ("row_id", Json.str row.rowId)
    , ("decl_name", Json.str row.declName)
    , ("module_name", Json.str row.moduleName)
    , ("decl_kind", Json.str row.declKind)
    , ("obligation_label", Json.str row.obligationLabel)
    , ("kind", Json.str row.kind.code)
    , ("primary_expr", stagedExprToJson row.primaryExpr)
    , ("secondary_expr", jsonExprOption row.secondaryExpr?)
    , ("target_type", stagedExprToJson row.targetType)
    , ("target_value", jsonExprOption row.targetValue?)
    , ("local_context", jsonExprArray row.localContext)
    ]

private def contractTagCode : KernelContractTag → String
  | .infer => "infer"
  | .inferSort => "infer_sort"
  | .check => "check"
  | .whnf => "whnf"
  | .defeq => "defeq"

private partial def cTypeToJson (ty : CType) : Json :=
  match ty with
  | .int => Json.mkObj [("tag", Json.str "int")]
  | .intSized signedness size =>
      Json.mkObj
        [ ("tag", Json.str "int_sized")
        , ("signedness", Json.str (reprStr signedness))
        , ("size", Json.str (reprStr size))
        ]
  | .ptr ty' => Json.mkObj [("tag", Json.str "ptr"), ("to", cTypeToJson ty')]
  | .array ty' n => Json.mkObj [("tag", Json.str "array"), ("elem", cTypeToJson ty'), ("length", toJson n)]
  | .funcPtr ret args =>
      Json.mkObj
        [ ("tag", Json.str "func_ptr")
        , ("ret", cTypeToJson ret)
        , ("args", Json.arr <| args.toArray.map cTypeToJson)
        ]
  | .struct name => Json.mkObj [("tag", Json.str "struct"), ("name", Json.str name)]
  | .union name => Json.mkObj [("tag", Json.str "union"), ("name", Json.str name)]
  | .enum name => Json.mkObj [("tag", Json.str "enum"), ("name", Json.str name)]
  | .typedef name => Json.mkObj [("tag", Json.str "typedef"), ("name", Json.str name)]
  | .void => Json.mkObj [("tag", Json.str "void")]

private def carrierValueToJson : KernelCarrierValue → Json
  | .cstring value =>
      Json.mkObj [("tag", Json.str "cstring"), ("value", Json.str value)]
  | .opTag value =>
      Json.mkObj [("tag", Json.str "op_tag"), ("value", Json.str (contractTagCode value))]
  | .exprRef value =>
      Json.mkObj [("tag", Json.str "expr_ref"), ("value", stagedExprToJson value)]
  | .exprOptRef value =>
      Json.mkObj [("tag", Json.str "expr_opt_ref"), ("value", jsonExprOption value)]
  | .exprSlice values =>
      Json.mkObj [("tag", Json.str "expr_slice"), ("value", jsonExprArray values)]

def leanCPFieldToJson (field : LeanCPField) : Json :=
  Json.mkObj
    [ ("name", Json.str field.name)
    , ("c_type", cTypeToJson field.cType)
    , ("value", carrierValueToJson field.value)
    ]

def leanCPContractRowToJson (row : LeanCPContractRow) : Json :=
  Json.mkObj
    [ ("struct_name", Json.str row.structName)
    , ("row_id", Json.str row.rowId)
    , ("decl_name", Json.str row.declName)
    , ("module_name", Json.str row.moduleName)
    , ("decl_kind", Json.str row.declKind)
    , ("obligation_label", Json.str row.obligationLabel)
    , ("op_tag", Json.str (contractTagCode row.opTag))
    , ("primary_expr", stagedExprToJson row.primaryExpr)
    , ("secondary_expr", jsonExprOption row.secondaryExpr?)
    , ("target_type", stagedExprToJson row.targetType)
    , ("target_value", jsonExprOption row.targetValue?)
    , ("local_context", jsonExprArray row.localContext)
    , ("layout", Json.arr <| leanCPCarrierLayout.toArray.map fun (name, cty) =>
        Json.mkObj [("name", Json.str name), ("c_type", cTypeToJson cty)])
    , ("fields", Json.arr <| row.fields.toArray.map leanCPFieldToJson)
    ]

def cContractRowToJson (row : CContractRow) : Json :=
  Json.mkObj
    [ ("row_id", Json.str row.rowId)
    , ("decl_name", Json.str row.declName)
    , ("module_name", Json.str row.moduleName)
    , ("decl_kind", Json.str row.declKind)
    , ("obligation_label", Json.str row.obligationLabel)
    , ("op_tag", Json.str (contractTagCode row.opTag))
    , ("primary_expr", stagedExprToJson row.primaryExpr)
    , ("secondary_expr", jsonExprOption row.secondaryExpr?)
    , ("target_type", stagedExprToJson row.targetType)
    , ("target_value", jsonExprOption row.targetValue?)
    , ("local_context", jsonExprArray row.localContext)
    ]

def rustMirrorRowToJson (row : RustMirrorRow) : Json :=
  cContractRowToJson
    { rowId := row.rowId
      declName := row.declName
      moduleName := row.moduleName
      declKind := row.declKind
      obligationLabel := row.obligationLabel
      opTag := row.opTag
      primaryExpr := row.primaryExpr
      secondaryExpr? := row.secondaryExpr?
      targetType := row.targetType
      targetValue? := row.targetValue?
      localContext := row.localContext }

def gpuKernelRowToJson (row : GPUKernelRow) : Json :=
  cContractRowToJson
    { rowId := row.rowId
      declName := row.declName
      moduleName := row.moduleName
      declKind := row.declKind
      obligationLabel := row.obligationLabel
      opTag := row.opTag
      primaryExpr := row.primaryExpr
      secondaryExpr? := row.secondaryExpr?
      targetType := row.targetType
      targetValue? := row.targetValue?
      localContext := row.localContext }

private def divergenceLayerCode : KernelDivergenceLayer → String
  | .none => "none"
  | .leanToCExport => "lean_to_c_export"
  | .cToLeanCPContract => "c_to_leancp_contract"
  | .cToRustIngest => "c_to_rust_ingest"
  | .rustToGPUProjection => "rust_to_gpu_projection"
  | .gpuExecution => "gpu_execution"
  | .timeoutOrResource => "timeout_or_resource"

private def verdictCode : KernelVerdict → String
  | .matched => "matched"
  | .unsupported => "unsupported"
  | .mismatch => "mismatch"
  | .timeout => "timeout"

def kernelOverlayRowToJson (row : KernelOverlayRow) : Json :=
  Json.mkObj
    [ ("row_id", Json.str row.rowId)
    , ("decl_name", Json.str row.declName)
    , ("module_name", Json.str row.moduleName)
    , ("obligation_label", Json.str row.obligationLabel)
    , ("kind", Json.str row.kind.code)
    , ("divergence_layer", Json.str (divergenceLayerCode row.divergenceLayer))
    , ("cpu_verdict", Json.str (verdictCode row.cpuVerdict))
    , ("rust_verdict", Json.str (verdictCode row.rustVerdict))
    , ("gpu_verdict", Json.str (verdictCode row.gpuVerdict))
    , ("canonical", canonicalObligationRowToJson row.canonical)
    , ("c_contract", cContractRowToJson row.cContract)
    , ("lean_cp_contract", leanCPContractRowToJson row.leanCPContract)
    , ("rust_mirror", rustMirrorRowToJson row.rustMirror)
    , ("gpu_kernel", gpuKernelRowToJson row.gpuKernel)
    ]

def kernelMappingArtifactToJson (artifact : KernelMappingArtifact) : Json :=
  Json.mkObj
    [ ("schema_version", toJson artifact.schemaVersion)
    , ("tool", Json.str artifact.tool)
    , ("summary",
        Json.mkObj
          [ ("canonical_rows", toJson artifact.summary.canonicalRows)
          , ("overlay_rows", toJson artifact.summary.overlayRows)
          ])
    , ("rows", Json.arr <| artifact.rows.toArray.map kernelOverlayRowToJson)
    ]

end LeanKernel
end LoF
end HeytingLean
