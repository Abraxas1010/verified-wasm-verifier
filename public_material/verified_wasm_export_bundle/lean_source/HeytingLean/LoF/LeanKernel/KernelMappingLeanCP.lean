import HeytingLean.LeanCP.Lang.CSyntax
import HeytingLean.LoF.LeanKernel.KernelMappingC

namespace HeytingLean
namespace LoF
namespace LeanKernel

open HeytingLean.LeanCP

/-!
# KernelMappingLeanCP

LeanCP-owned typed carrier for the exported kernel contract row. This is the
code-facing semantic owner that the foreign C/Rust/GPU layers are expected to
mirror.
-/

inductive KernelCarrierValue where
  | cstring (value : String)
  | opTag (value : KernelContractTag)
  | exprRef (value : SExpr)
  | exprOptRef (value : Option SExpr)
  | exprSlice (value : List SExpr)
  deriving Repr, DecidableEq

def KernelCarrierValue.cType : KernelCarrierValue → CType
  | .cstring _ => .typedef "cstring"
  | .opTag _ => .typedef "kernel_op_tag"
  | .exprRef _ => .typedef "staged_expr_ref"
  | .exprOptRef _ => .typedef "staged_expr_ref"
  | .exprSlice _ => .typedef "staged_expr_slice"

structure LeanCPField where
  name : String
  cType : CType
  value : KernelCarrierValue
  deriving Repr

noncomputable instance : DecidableEq LeanCPField := Classical.decEq _

def LeanCPField.WellTyped (field : LeanCPField) : Prop :=
  field.cType = field.value.cType

structure LeanCPContractRow where
  structName : String := "kernel_contract_row"
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
  fields : List LeanCPField := []
  deriving Repr

noncomputable instance : DecidableEq LeanCPContractRow := Classical.decEq _

def leanCPCarrierLayout : List (String × CType) := cContractCarrierLayout

def leanCPFieldsOfContractRow (row : CContractRow) : List LeanCPField :=
  [ { name := "row_id", cType := .typedef "cstring", value := .cstring row.rowId }
  , { name := "decl_name", cType := .typedef "cstring", value := .cstring row.declName }
  , { name := "module_name", cType := .typedef "cstring", value := .cstring row.moduleName }
  , { name := "decl_kind", cType := .typedef "cstring", value := .cstring row.declKind }
  , { name := "obligation_label", cType := .typedef "cstring", value := .cstring row.obligationLabel }
  , { name := "op_tag", cType := .typedef "kernel_op_tag", value := .opTag row.opTag }
  , { name := "primary_expr", cType := .typedef "staged_expr_ref", value := .exprRef row.primaryExpr }
  , { name := "secondary_expr", cType := .typedef "staged_expr_ref", value := .exprOptRef row.secondaryExpr? }
  , { name := "target_type", cType := .typedef "staged_expr_ref", value := .exprRef row.targetType }
  , { name := "target_value", cType := .typedef "staged_expr_ref", value := .exprOptRef row.targetValue? }
  , { name := "local_context", cType := .typedef "staged_expr_slice", value := .exprSlice row.localContext }
  ]

def cContractToLeanCPContract (row : CContractRow) : LeanCPContractRow :=
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
    localContext := row.localContext
    fields := leanCPFieldsOfContractRow row }

def leanCPContractToCContract (row : LeanCPContractRow) : CContractRow :=
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

@[simp] theorem leanCPContractToCContract_cContractToLeanCPContract
    (row : CContractRow) :
    leanCPContractToCContract (cContractToLeanCPContract row) = row := by
  cases row
  rfl

@[simp] theorem cContractToLeanCPContract_leanCPContractToCContract
    (row : LeanCPContractRow) :
    cContractToLeanCPContract (leanCPContractToCContract row) =
      { row with
          structName := "kernel_contract_row"
          fields := leanCPFieldsOfContractRow (leanCPContractToCContract row) } := by
  cases row
  simp [cContractToLeanCPContract, leanCPContractToCContract, leanCPFieldsOfContractRow]

@[simp] theorem leanCPCarrierLayout_length :
    leanCPCarrierLayout.length = 11 := rfl

@[simp] theorem leanCPFieldsOfContractRow_length (row : CContractRow) :
    (leanCPFieldsOfContractRow row).length = leanCPCarrierLayout.length := by
  simp [leanCPFieldsOfContractRow, leanCPCarrierLayout]

theorem leanCPFieldsOfContractRow_wellTyped
    (row : CContractRow) :
    ∀ field ∈ leanCPFieldsOfContractRow row, field.WellTyped := by
  intro field hmem
  simp [leanCPFieldsOfContractRow] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

@[simp] theorem cContractToLeanCPContract_fields
    (row : CContractRow) :
    (cContractToLeanCPContract row).fields = leanCPFieldsOfContractRow row := rfl

@[simp] theorem cContractToLeanCPContract_structName
    (row : CContractRow) :
    (cContractToLeanCPContract row).structName = "kernel_contract_row" := rfl

end LeanKernel
end LoF
end HeytingLean
