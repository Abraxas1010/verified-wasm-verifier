import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Nat.Basic

/-!
# Knot theory: Artin braid groups (Phase 4, formal)

This module defines the Artin braid group `Bₙ` as a presented group with generators
`σᵢ` for `i = 0..n-2` and the standard relations:

* `σᵢ σⱼ = σⱼ σᵢ` for `|i-j| ≥ 2`,
* `σᵢ σᵢ₊₁ σᵢ = σᵢ₊₁ σᵢ σᵢ₊₁` for `i = 0..n-3`.

The goal is to provide a theorem-level object to complement the executable braid-word
layer in `HeytingLean.Topology.Knot.Braid`.
-/

namespace HeytingLean
namespace Topology
namespace Knot

open PresentedGroup

namespace ArtinBraid

/-- Generator indices for `Bₙ`: `0..n-2` (0-based). -/
abbrev Gen (n : Nat) : Type :=
  Fin (n - 1)

def fgOf {n : Nat} (i : Gen n) : FreeGroup (Gen n) :=
  FreeGroup.of i

def fgNat (n i : Nat) (hi : i < n - 1) : FreeGroup (Gen n) :=
  fgOf (n := n) ⟨i, hi⟩

/-- Far-commutation relator: `(σᵢ σⱼ) (σⱼ σᵢ)⁻¹`. -/
def commRelator (n i j : Nat) (hi : i < n - 1) (hj : j < n - 1) :
    FreeGroup (Gen n) :=
  let lhs := fgNat n i hi * fgNat n j hj
  let rhs := fgNat n j hj * fgNat n i hi
  lhs * rhs⁻¹

theorem lt_sub_one_of_succ_lt {n i : Nat} (h : i.succ < n) : i < n - 1 := by
  have : i < n.pred := (Nat.lt_pred_iff).2 h
  simpa [Nat.pred_eq_sub_one] using this

/-- Braid relator: `(σᵢ σᵢ₊₁ σᵢ) (σᵢ₊₁ σᵢ σᵢ₊₁)⁻¹` for `i+2 < n`. -/
def braidRelator (n i : Nat) (hi : i + 2 < n) : FreeGroup (Gen n) :=
  let hi0 : i < n - 1 :=
    lt_sub_one_of_succ_lt (n := n) (i := i) <|
      Nat.lt_trans (Nat.lt_succ_self (i + 1)) hi
  let hi1 : i + 1 < n - 1 :=
    lt_sub_one_of_succ_lt (n := n) (i := i + 1) <| by
      simpa [Nat.add_assoc, Nat.succ_eq_add_one] using hi
  let σi := fgNat n i hi0
  let σi1 := fgNat n (i + 1) hi1
  let lhs := σi * σi1 * σi
  let rhs := σi1 * σi * σi1
  lhs * rhs⁻¹

/-- The Artin braid relations for `Bₙ`. -/
def rels (n : Nat) : Set (FreeGroup (Gen n)) :=
  { r |
      ∃ (i j : Nat) (hi : i < n - 1) (hj : j < n - 1),
        (i + 1 < j ∨ j + 1 < i) ∧ r = commRelator n i j hi hj } ∪
    { r | ∃ (i : Nat) (hi : i + 2 < n), r = braidRelator n i hi }

/-- The Artin braid group `Bₙ` as a presented group. -/
abbrev BraidGroup (n : Nat) : Type :=
  PresentedGroup (rels n)

/-- The standard generator `σᵢ : Bₙ`. -/
def sigma {n : Nat} (i : Gen n) : BraidGroup n :=
  PresentedGroup.of i

namespace BraidGroup

/-- Far commutation: `σᵢ σⱼ = σⱼ σᵢ` when `|i-j| ≥ 2`. -/
theorem sigma_comm {n i j : Nat} (hi : i < n - 1) (hj : j < n - 1)
    (hfar : i + 1 < j ∨ j + 1 < i) :
    sigma (n := n) ⟨i, hi⟩ * sigma ⟨j, hj⟩ = sigma ⟨j, hj⟩ * sigma ⟨i, hi⟩ := by
  classical
  have hx :
      (fgNat n i hi * fgNat n j hj) * (fgNat n j hj * fgNat n i hi)⁻¹ ∈ rels n := by
    refine Or.inl ?_
    exact ⟨i, j, hi, hj, hfar, rfl⟩
  simpa [sigma, PresentedGroup.of, fgNat, fgOf, mul_assoc] using
    (PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := rels n) (x := fgNat n i hi * fgNat n j hj)
      (y := fgNat n j hj * fgNat n i hi) hx)

/-- Braid relation: `σᵢ σᵢ₊₁ σᵢ = σᵢ₊₁ σᵢ σᵢ₊₁` for `i+2 < n`. -/
theorem sigma_braid {n i : Nat} (hi : i + 2 < n) :
    let hi0 : i < n - 1 :=
      lt_sub_one_of_succ_lt (n := n) (i := i) <|
        Nat.lt_trans (Nat.lt_succ_self (i + 1)) hi
    let hi1 : i + 1 < n - 1 :=
      lt_sub_one_of_succ_lt (n := n) (i := i + 1) <| by
        simpa [Nat.add_assoc, Nat.succ_eq_add_one] using hi
    sigma (n := n) ⟨i, hi0⟩ * sigma ⟨i + 1, hi1⟩ * sigma ⟨i, hi0⟩ =
      sigma ⟨i + 1, hi1⟩ * sigma ⟨i, hi0⟩ * sigma ⟨i + 1, hi1⟩ := by
  classical
  -- Unfold the local indices and use the relator.
  simp (config := { zeta := false }) only
  intro hi0 hi1
  have hx : braidRelator n i hi ∈ rels n := by
    refine Or.inr ?_
    exact ⟨i, hi, rfl⟩
  -- `braidRelator` is `lhs * rhs⁻¹`, so `mk` identifies `lhs` and `rhs`.
  have hmk :
      (mk (rels n)) (fgNat n i hi0 * fgNat n (i + 1) hi1 * fgNat n i hi0) =
        (mk (rels n)) (fgNat n (i + 1) hi1 * fgNat n i hi0 * fgNat n (i + 1) hi1) := by
    -- `braidRelator` is definitionally `x * y⁻¹` with these `x` and `y`.
    simpa [braidRelator, hi0, hi1, mul_assoc] using
      (PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := rels n)
        (x := fgNat n i hi0 * fgNat n (i + 1) hi1 * fgNat n i hi0)
        (y := fgNat n (i + 1) hi1 * fgNat n i hi0 * fgNat n (i + 1) hi1) hx)
  simpa [sigma, PresentedGroup.of, fgNat, fgOf, mul_assoc] using hmk

end BraidGroup

end ArtinBraid

end Knot
end Topology
end HeytingLean
