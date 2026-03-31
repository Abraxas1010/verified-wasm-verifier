import HeytingLean.LeanCP.Lang.CSyntax
import HeytingLean.LoF.LeanKernel.KernelMapping

namespace HeytingLean
namespace LoF
namespace LeanKernel

open HeytingLean.LeanCP

/-!
# KernelMappingC

C-compatible, Rust-compatible, and GPU-launch-compatible projections of the
canonical Lean row. These rows are the foreign implementation targets.
-/

inductive KernelContractTag where
  | infer
  | inferSort
  | check
  | whnf
  | defeq
  deriving Repr, DecidableEq

def KernelContractTag.ofKind : KernelObligationKind → KernelContractTag
  | .infer => .infer
  | .inferSort => .inferSort
  | .check => .check
  | .whnf => .whnf
  | .defeq => .defeq

def KernelContractTag.toKind : KernelContractTag → KernelObligationKind
  | .infer => .infer
  | .inferSort => .inferSort
  | .check => .check
  | .whnf => .whnf
  | .defeq => .defeq

@[simp] theorem KernelContractTag.toKind_ofKind (kind : KernelObligationKind) :
    (KernelContractTag.ofKind kind).toKind = kind := by
  cases kind <;> rfl

@[simp] theorem KernelContractTag.ofKind_toKind (tag : KernelContractTag) :
    KernelContractTag.ofKind tag.toKind = tag := by
  cases tag <;> rfl

structure CContractRow where
  rowId : String
  declName : String
  moduleName : String
  declKind : String
  obligationLabel : String
  opTag : KernelContractTag
  primaryExpr : SExpr
  secondaryExpr? : Option SExpr := none
  targetType : SExpr
  targetValue? : Option SExpr := none
  localContext : List SExpr := []
  deriving Repr, DecidableEq

def canonicalToCContract (row : CanonicalObligationRow) : CContractRow :=
  { rowId := row.rowId
    declName := row.declName
    moduleName := row.moduleName
    declKind := row.declKind
    obligationLabel := row.obligationLabel
    opTag := KernelContractTag.ofKind row.kind
    primaryExpr := row.primaryExpr
    secondaryExpr? := row.secondaryExpr?
    targetType := row.targetType
    targetValue? := row.targetValue?
    localContext := row.localContext }

def cContractToCanonical (row : CContractRow) : CanonicalObligationRow :=
  { rowId := row.rowId
    declName := row.declName
    moduleName := row.moduleName
    declKind := row.declKind
    obligationLabel := row.obligationLabel
    kind := row.opTag.toKind
    primaryExpr := row.primaryExpr
    secondaryExpr? := row.secondaryExpr?
    targetType := row.targetType
    targetValue? := row.targetValue?
    localContext := row.localContext }

@[simp] theorem cContractToCanonical_canonicalToCContract
    (row : CanonicalObligationRow) :
    cContractToCanonical (canonicalToCContract row) = row := by
  cases row
  simp [canonicalToCContract, cContractToCanonical]

@[simp] theorem canonicalToCContract_cContractToCanonical
    (row : CContractRow) :
    canonicalToCContract (cContractToCanonical row) = row := by
  cases row
  simp [canonicalToCContract, cContractToCanonical]

structure RustMirrorRow where
  rowId : String
  declName : String
  moduleName : String
  declKind : String
  obligationLabel : String
  opTag : KernelContractTag
  primaryExpr : SExpr
  secondaryExpr? : Option SExpr := none
  targetType : SExpr
  targetValue? : Option SExpr := none
  localContext : List SExpr := []
  deriving Repr, DecidableEq

def cContractToRustMirror (row : CContractRow) : RustMirrorRow :=
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

def rustMirrorToCContract (row : RustMirrorRow) : CContractRow :=
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

@[simp] theorem rustMirrorToCContract_cContractToRustMirror
    (row : CContractRow) :
    rustMirrorToCContract (cContractToRustMirror row) = row := by
  cases row
  rfl

@[simp] theorem cContractToRustMirror_rustMirrorToCContract
    (row : RustMirrorRow) :
    cContractToRustMirror (rustMirrorToCContract row) = row := by
  cases row
  rfl

structure GPUKernelRow where
  rowId : String
  declName : String
  moduleName : String
  declKind : String
  obligationLabel : String
  opTag : KernelContractTag
  primaryExpr : SExpr
  secondaryExpr? : Option SExpr := none
  targetType : SExpr
  targetValue? : Option SExpr := none
  localContext : List SExpr := []
  deriving Repr, DecidableEq

def rustMirrorToGPUKernel (row : RustMirrorRow) : GPUKernelRow :=
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

def gpuKernelToRustMirror (row : GPUKernelRow) : RustMirrorRow :=
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

@[simp] theorem gpuKernelToRustMirror_rustMirrorToGPUKernel
    (row : RustMirrorRow) :
    gpuKernelToRustMirror (rustMirrorToGPUKernel row) = row := by
  cases row
  rfl

@[simp] theorem rustMirrorToGPUKernel_gpuKernelToRustMirror
    (row : GPUKernelRow) :
    rustMirrorToGPUKernel (gpuKernelToRustMirror row) = row := by
  cases row
  rfl

def cContractCarrierLayout : List (String × CType) :=
  [ ("row_id", .typedef "cstring")
  , ("decl_name", .typedef "cstring")
  , ("module_name", .typedef "cstring")
  , ("decl_kind", .typedef "cstring")
  , ("obligation_label", .typedef "cstring")
  , ("op_tag", .typedef "kernel_op_tag")
  , ("primary_expr", .typedef "staged_expr_ref")
  , ("secondary_expr", .typedef "staged_expr_ref")
  , ("target_type", .typedef "staged_expr_ref")
  , ("target_value", .typedef "staged_expr_ref")
  , ("local_context", .typedef "staged_expr_slice")
  ]

def rustMirrorCarrierLayout : List (String × CType) := cContractCarrierLayout

def gpuKernelCarrierLayout : List (String × CType) := cContractCarrierLayout

@[simp] theorem cContractCarrierLayout_length :
    cContractCarrierLayout.length = 11 := rfl

@[simp] theorem rustMirrorCarrierLayout_length :
    rustMirrorCarrierLayout.length = 11 := rfl

@[simp] theorem gpuKernelCarrierLayout_length :
    gpuKernelCarrierLayout.length = 11 := rfl

end LeanKernel
end LoF
end HeytingLean
