import HeytingLean.Layouts
import Mathlib.Data.List.Basic

/-!
# λ-IR Layout Annotations (scaffold)

This module introduces a small, layout-aware intermediate language intended for *code generation*
demos (Plain C and CUTLASS-flavored C++).

It intentionally does **not** modify the existing, typed `HeytingLean.LambdaIR` fragment.
Instead it provides a lightweight IR that can later be connected to the typed pipeline.
-/

namespace HeytingLean
namespace Compilation
namespace LambdaIR

/-- Layout annotation for tensors (shape/stride + static-vs-runtime flag). -/
structure LayoutAnnotation where
  shape : List Nat
  stride : List Nat
  /-- `true` = compile-time known (emit `#define`s), `false` = runtime (emit struct + loops). -/
  isStatic : Bool
  /-- Well-formedness: same rank for shape and stride. -/
  shape_stride_len : shape.length = stride.length
  deriving Repr

namespace LayoutAnnotation

/-- Rank (number of axes). -/
def rank (L : LayoutAnnotation) : Nat := L.shape.length

/-- Total size (product of shapes). -/
def size (L : LayoutAnnotation) : Nat :=
  L.shape.foldl (fun acc s => acc * s) 1

/-- Boolean well-formedness check: same rank and all shape entries positive. -/
def wellFormedB (L : LayoutAnnotation) : Bool :=
  decide (L.shape.length = L.stride.length) &&
    L.shape.all (fun s => decide (0 < s))

@[simp] theorem rank_eq (L : LayoutAnnotation) : L.rank = L.shape.length := rfl

/-- Convert a CuTe flat layout to a static `LayoutAnnotation`. -/
def ofFlatLayout (L : HeytingLean.Layouts.Flat.FlatLayout) : LayoutAnnotation :=
  { shape := L.map (fun p => p.shapeNat)
    stride := L.map (fun p => p.stride)
    isStatic := true
    shape_stride_len := by simp }

end LayoutAnnotation

/-- A minimal layout-aware type language. -/
inductive LType
  | nat : LType
  | bool : LType
  | fn : LType → LType → LType
  | tensor : LType → LayoutAnnotation → LType
  | pair : LType → LType → LType
  deriving Repr

/-- A minimal layout-aware expression language. -/
inductive LExpr
  | var : String → LExpr
  | lam : String → LType → LExpr → LExpr
  | app : LExpr → LExpr → LExpr
  | lit : Nat → LExpr
  -- Tensor operations (layout-aware)
  | tensorAlloc : LayoutAnnotation → LExpr
  | tensorIndex : LExpr → List LExpr → LExpr
  | tensorStore : LExpr → List LExpr → LExpr → LExpr
  -- Layout operations (compile to index arithmetic)
  | layoutCompose : LayoutAnnotation → LayoutAnnotation → LExpr
  | layoutCoalesce : LayoutAnnotation → LExpr
  deriving Repr

/-- Proof certificate attached to layout operations (externalized). -/
structure LayoutCertificate where
  operation : String
  inputLayouts : List LayoutAnnotation
  outputLayout : LayoutAnnotation
  proofHash : String
  deriving Repr

/-- Annotated λ-IR term with a list of layout certificates. -/
structure AnnotatedExpr where
  expr : LExpr
  certificates : List LayoutCertificate
  deriving Repr

end LambdaIR
end Compilation
end HeytingLean
