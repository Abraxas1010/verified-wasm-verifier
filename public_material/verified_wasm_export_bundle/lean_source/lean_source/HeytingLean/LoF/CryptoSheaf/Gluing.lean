import HeytingLean.LoF.CryptoSheaf.Descent

/-
CryptoSheaf/Gluing

Concrete Ωᴿ-level gluing operations via joins and meets over lists.
-/

namespace HeytingLean
namespace LoF
namespace CryptoSheaf

open HeytingLean.LoF

variable {α : Type u} [PrimaryAlgebra α]

variable (R : Reentry α)

/-- Additive gluing: fold by join starting from ⊥ in Ωᴿ. -/
def additiveGlue (pieces : List R.Omega) : R.Omega :=
  pieces.foldl (· ⊔ ·) ⊥

/-- Multiplicative gluing: fold by meet starting from ⊤ in Ωᴿ. -/
def multiplicativeGlue (pieces : List R.Omega) : R.Omega :=
  pieces.foldl (· ⊓ ·) ⊤

/-! ## Optional: threshold-style gluing

Two variants are provided:
1. A tiny record `ThresholdGlue` with a single `aggregate` using meet.
2. A lightweight `thresholdGlue k pieces` that returns `⊥` unless enough
   pieces are provided; otherwise it reduces to `multiplicativeGlue`.
-/

structure ThresholdGlue (R : Reentry α) where
  k : Nat
  pieces : List R.Omega

/-- Current placeholder aggregation for a threshold family (meet of all pieces). -/
def ThresholdGlue.aggregate (tg : ThresholdGlue R) : R.Omega :=
  multiplicativeGlue (R := R) tg.pieces

/-- Lightweight threshold semantics: require at least `k` pieces. -/
def thresholdGlue (k : Nat) (pieces : List R.Omega) : R.Omega :=
  if _ : k ≤ pieces.length then multiplicativeGlue (R := R) pieces else ⊥

@[simp] lemma thresholdGlue_nil_zero : thresholdGlue (R := R) 0 [] = (⊤ : R.Omega) := by
  simp [thresholdGlue, multiplicativeGlue]

@[simp] lemma thresholdGlue_nil_succ (k : Nat) : thresholdGlue (R := R) (k.succ) [] = (⊥ : R.Omega) := by
  simp [thresholdGlue]

/-! ## A slightly richer variant: meet the first `k` pieces if available. -/

def thresholdGlueTake (k : Nat) (pieces : List R.Omega) : R.Omega :=
  if _ : k ≤ pieces.length then
    multiplicativeGlue (R := R) (pieces.take k)
  else
    ⊥

@[simp] lemma thresholdGlueTake_zero (pieces : List R.Omega) :
    thresholdGlueTake (R := R) 0 pieces = (⊤ : R.Omega) := by
  simp [thresholdGlueTake, multiplicativeGlue]

@[simp] lemma thresholdGlueTake_nil_succ (k : Nat) :
    thresholdGlueTake (R := R) (k.succ) [] = (⊥ : R.Omega) := by
  simp [thresholdGlueTake]

end CryptoSheaf
end LoF
end HeytingLean
