import HeytingLean.Compilation.Codegen.Unified
import HeytingLean.Layouts
import HeytingLean.Layouts.Flat.Tractable
import HeytingLean.Util.SHA
import Mathlib.Tactic

/-!
# Verified matrix multiplication (layout/codegen demo)

This is an *end-to-end wiring example* for the extension modules:
- define standard 2D CuTe layouts,
- prove tractability in the flat setting,
- generate a hybrid (Plain C + CUTLASS header) code bundle.

It is intentionally lightweight: code generation emits deterministic text artifacts; the “typed tensor IR”
integration is deferred to later work.
-/

namespace HeytingLean
namespace Examples
namespace MatMul

open HeytingLean.Layouts
open HeytingLean.Layouts.Flat

/-- Layout for an `M×K` matrix `A` (column-major). -/
def layoutA (M K : ℕ+) : FlatLayout :=
  [ShapeStridePair.mk M 1, ShapeStridePair.mk K M.val]

/-- Layout for a `K×N` matrix `B` (row-major). -/
def layoutB (K N : ℕ+) : FlatLayout :=
  [ShapeStridePair.mk K N.val, ShapeStridePair.mk N 1]

/-- Layout for an `M×N` matrix `C` (row-major). -/
def layoutC (M N : ℕ+) : FlatLayout :=
  [ShapeStridePair.mk M N.val, ShapeStridePair.mk N 1]

private theorem layoutA_tractable (M K : ℕ+) : FlatLayout.Tractable (layoutA M K) := by
  intro i j hij hle _hsi _hsj
  classical
  fin_cases i <;> fin_cases j
  · cases hij rfl
  · simp [layoutA]
  ·
    have hle' : M.val < 1 ∨ (M.val = 1 ∧ K.val ≤ M.val) := by
      simpa [layoutA, ShapeStridePair.le] using hle
    cases hle' with
    | inl hlt =>
        have hMge : 1 ≤ M.val := Nat.succ_le_iff.mpr (PNat.pos M)
        exact (Nat.not_lt_of_ge hMge hlt).elim
    | inr h =>
        rcases h with ⟨hM1, hKle⟩
        have hKle' : K.val ≤ 1 := by simpa [hM1] using hKle
        have hKge : 1 ≤ K.val := Nat.succ_le_iff.mpr (PNat.pos K)
        have hK1 : K.val = 1 := Nat.le_antisymm hKle' hKge
        simp [layoutA, hM1, hK1]
  · cases hij rfl

private theorem layoutB_tractable (K N : ℕ+) : FlatLayout.Tractable (layoutB K N) := by
  intro i j hij hle _hsi _hsj
  classical
  fin_cases i <;> fin_cases j
  · cases hij rfl
  ·
    have hle' : N.val < 1 ∨ (N.val = 1 ∧ K.val ≤ N.val) := by
      simpa [layoutB, ShapeStridePair.le] using hle
    cases hle' with
    | inl hlt =>
        have hNge : 1 ≤ N.val := Nat.succ_le_iff.mpr (PNat.pos N)
        exact (Nat.not_lt_of_ge hNge hlt).elim
    | inr h =>
        rcases h with ⟨hN1, hKle⟩
        have hKle' : K.val ≤ 1 := by simpa [hN1] using hKle
        have hKge : 1 ≤ K.val := Nat.succ_le_iff.mpr (PNat.pos K)
        have hK1 : K.val = 1 := Nat.le_antisymm hKle' hKge
        simp [layoutB, hN1, hK1]
  · simp [layoutB]
  · cases hij rfl

private theorem layoutC_tractable (M N : ℕ+) : FlatLayout.Tractable (layoutC M N) := by
  intro i j hij hle _hsi _hsj
  classical
  fin_cases i <;> fin_cases j
  · cases hij rfl
  ·
    have hle' : N.val < 1 ∨ (N.val = 1 ∧ M.val ≤ N.val) := by
      simpa [layoutC, ShapeStridePair.le] using hle
    cases hle' with
    | inl hlt =>
        have hNge : 1 ≤ N.val := Nat.succ_le_iff.mpr (PNat.pos N)
        exact (Nat.not_lt_of_ge hNge hlt).elim
    | inr h =>
        rcases h with ⟨hN1, hMle⟩
        have hMle' : M.val ≤ 1 := by simpa [hN1] using hMle
        have hMge : 1 ≤ M.val := Nat.succ_le_iff.mpr (PNat.pos M)
        have hM1 : M.val = 1 := Nat.le_antisymm hMle' hMge
        simp [layoutC, hN1, hM1]
  · simp [layoutC]
  · cases hij rfl

/-- The standard matmul layouts are tractable (flat setting). -/
theorem layouts_tractable (M K N : ℕ+) :
    FlatLayout.Tractable (layoutA M K) ∧
    FlatLayout.Tractable (layoutB K N) ∧
    FlatLayout.Tractable (layoutC M N) := by
  exact ⟨layoutA_tractable M K, layoutB_tractable K N, layoutC_tractable M N⟩

/-- Generate a verified (certificate-carrying) code bundle for matmul layouts. -/
def generateMatMulCode (M K N : ℕ+) : IO Compilation.Codegen.GeneratedCode := do
  let layoutAAnn : Compilation.LambdaIR.LayoutAnnotation :=
    { shape := [M.val, K.val]
      stride := [1, M.val]
      isStatic := true
      shape_stride_len := rfl }
  let layoutBAnn : Compilation.LambdaIR.LayoutAnnotation :=
    { shape := [K.val, N.val]
      stride := [N.val, 1]
      isStatic := true
      shape_stride_len := rfl }
  let layoutCAnn : Compilation.LambdaIR.LayoutAnnotation :=
    { shape := [M.val, N.val]
      stride := [N.val, 1]
      isStatic := true
      shape_stride_len := rfl }
  let layouts : List (String × Compilation.LambdaIR.LayoutAnnotation) :=
    [ ("LayoutA", layoutAAnn), ("LayoutB", layoutBAnn), ("LayoutC", layoutCAnn) ]

  let proofMaterial :=
    s!"MatMul.layouts_tractable|M={M.val}|K={K.val}|N={N.val}|A.shape={layoutAAnn.shape}|A.stride={layoutAAnn.stride}|B.shape={layoutBAnn.shape}|B.stride={layoutBAnn.stride}|C.shape={layoutCAnn.shape}|C.stride={layoutCAnn.stride}"
  let proofHash := "sha256:" ++ (← HeytingLean.Util.sha256HexOfStringIO proofMaterial)

  let certs : List Compilation.LambdaIR.LayoutCertificate :=
    [ { operation := "tractability(flat)"
        inputLayouts := layouts.map (·.2)
        outputLayout := layoutCAnn
        proofHash := proofHash } ]

  Compilation.Codegen.generateCode
    { backend := .Hybrid
      moduleName := "matmul"
      emitCertificates := true
      staticLayouts := true }
    [] layouts certs

end MatMul
end Examples
end HeytingLean
