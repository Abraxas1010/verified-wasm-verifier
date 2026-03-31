import HeytingLean.Crypto.KEM.MLKEMResidualAccurate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# ML-KEM residual: deterministic coefficient bounds (Gap 3 support)

This file proves **deterministic** (worst-case) coefficient bounds for the “accurate-shape”
negacyclic convolution residual model from `MLKEMResidualAccurate.lean`.

These bounds do *not* provide a failure probability, but they are useful glue for later steps:
- bounding the support/range for DP-style exact computations, and
- making the “sum of products” structure explicit for future probability assumptions.
-/

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203

open scoped BigOperators

namespace ResidualBounds

open ResidualAccurate

variable {n k : Nat}

/-- Dot product of `k` ring multiplications (coefficient-level), where multiplication is negacyclic convolution. -/
noncomputable def dotNegacyclicCoeff (n : Nat) (hn : 0 < n) (k : Nat)
    (x y : Fin k → Fin n → ℤ) (i : Fin n) : ℤ :=
  ∑ t : Fin k, negacyclicConvCoeff n hn (x t) (y t) i

theorem natAbs_dotNegacyclicCoeff_le (n : Nat) (hn : 0 < n) (k : Nat)
    (x y : Fin k → Fin n → ℤ) (i : Fin n)
    (A B : Nat)
    (hx : ∀ t j, (x t j).natAbs ≤ A)
    (hy : ∀ t j, (y t j).natAbs ≤ B) :
    (dotNegacyclicCoeff n hn k x y i).natAbs ≤ k * (n * A * B) := by
  classical
  -- Bound the absolute value by the sum of absolute values.
  have h1 :
      (dotNegacyclicCoeff n hn k x y i).natAbs ≤
        ∑ t : Fin k, (negacyclicConvCoeff n hn (x t) (y t) i).natAbs := by
    simpa [dotNegacyclicCoeff] using
      (nat_abs_sum_le (s := (Finset.univ : Finset (Fin k)))
        (f := fun t : Fin k => negacyclicConvCoeff n hn (x t) (y t) i))
  -- Bound each term by `n*A*B`, then sum.
  have hterm : ∀ t : Fin k, (negacyclicConvCoeff n hn (x t) (y t) i).natAbs ≤ n * A * B := by
    intro t
    exact natAbs_negacyclicConvCoeff_le (n := n) (hn := hn) (a := x t) (b := y t) (i := i)
      (A := A) (B := B) (ha := hx t) (hb := hy t)
  have h2 :
      (∑ t : Fin k, (negacyclicConvCoeff n hn (x t) (y t) i).natAbs) ≤ k * (n * A * B) := by
    have :
        (∑ t : Fin k, (negacyclicConvCoeff n hn (x t) (y t) i).natAbs) ≤ ∑ _t : Fin k, (n * A * B) := by
      refine Finset.sum_le_sum ?_
      intro t _ht
      exact hterm t
    simpa using (this.trans_eq (by simp))
  exact le_trans h1 h2

/-!
## Residual bound template

If coefficient-wise bounds are provided for the noise vectors, the residual coefficient
`⟨e,r⟩ + e₂ - ⟨s,e₁⟩` is bounded by combining the dot bounds and the `natAbs_add` / `natAbs_sub` lemmas.
-/

theorem natAbs_residualCoeff_le (n : Nat) (hn : 0 < n) (k : Nat)
    (e r s e1 : Fin k → Fin n → ℤ) (e2 : Fin n → ℤ) (i : Fin n)
    (Ae Ar As Ae1 Ae2 : Nat)
    (he : ∀ t j, (e t j).natAbs ≤ Ae)
    (hr : ∀ t j, (r t j).natAbs ≤ Ar)
    (hs : ∀ t j, (s t j).natAbs ≤ As)
    (he1 : ∀ t j, (e1 t j).natAbs ≤ Ae1)
    (he2 : ∀ j, (e2 j).natAbs ≤ Ae2) :
    ((dotNegacyclicCoeff n hn k e r i) + e2 i - (dotNegacyclicCoeff n hn k s e1 i)).natAbs ≤
      (k * (n * Ae * Ar)) + Ae2 + (k * (n * As * Ae1)) := by
  -- Bound `|x + y - z|` by `|x| + |y| + |z|`.
  have hx :
      (dotNegacyclicCoeff n hn k e r i).natAbs ≤ k * (n * Ae * Ar) :=
    natAbs_dotNegacyclicCoeff_le (n := n) (hn := hn) (k := k) (x := e) (y := r) (i := i)
      (A := Ae) (B := Ar) he hr
  have hy : (e2 i).natAbs ≤ Ae2 := he2 i
  have hz :
      (dotNegacyclicCoeff n hn k s e1 i).natAbs ≤ k * (n * As * Ae1) :=
    natAbs_dotNegacyclicCoeff_le (n := n) (hn := hn) (k := k) (x := s) (y := e1) (i := i)
      (A := As) (B := Ae1) hs he1
  -- Use `sub_eq_add_neg` and standard natAbs inequalities.
  have hsub :
      ((dotNegacyclicCoeff n hn k e r i) + e2 i - dotNegacyclicCoeff n hn k s e1 i).natAbs
        ≤ ((dotNegacyclicCoeff n hn k e r i) + e2 i).natAbs +
            (dotNegacyclicCoeff n hn k s e1 i).natAbs := by
    simpa [sub_eq_add_neg] using (Int.natAbs_add_le ((dotNegacyclicCoeff n hn k e r i) + e2 i) (-(dotNegacyclicCoeff n hn k s e1 i)))
  have hadd :
      ((dotNegacyclicCoeff n hn k e r i) + e2 i).natAbs ≤
        (dotNegacyclicCoeff n hn k e r i).natAbs + (e2 i).natAbs := by
    simpa using Int.natAbs_add_le (dotNegacyclicCoeff n hn k e r i) (e2 i)
  have :
      ((dotNegacyclicCoeff n hn k e r i) + e2 i - dotNegacyclicCoeff n hn k s e1 i).natAbs ≤
        (k * (n * Ae * Ar)) + Ae2 + (k * (n * As * Ae1)) := by
    calc
      ((dotNegacyclicCoeff n hn k e r i) + e2 i - dotNegacyclicCoeff n hn k s e1 i).natAbs
          ≤ ((dotNegacyclicCoeff n hn k e r i) + e2 i).natAbs +
              (dotNegacyclicCoeff n hn k s e1 i).natAbs := hsub
      _ ≤ ((dotNegacyclicCoeff n hn k e r i).natAbs + (e2 i).natAbs) +
              (dotNegacyclicCoeff n hn k s e1 i).natAbs := by
            exact Nat.add_le_add_right hadd _
      _ ≤ (k * (n * Ae * Ar) + Ae2) + (k * (n * As * Ae1)) := by
            refine Nat.add_le_add ?_ hz
            exact Nat.add_le_add hx hy
      _ = (k * (n * Ae * Ar)) + Ae2 + (k * (n * As * Ae1)) := by
            simp [Nat.add_assoc]
  simpa [sub_eq_add_neg] using this

theorem natAbs_residualCoeff_with_compression_le (n : Nat) (hn : 0 < n) (k : Nat)
    (e r s e1 : Fin k → Fin n → ℤ) (e2 comp : Fin n → ℤ) (i : Fin n)
    (Ae Ar As Ae1 Ae2 Acomp : Nat)
    (he : ∀ t j, (e t j).natAbs ≤ Ae)
    (hr : ∀ t j, (r t j).natAbs ≤ Ar)
    (hs : ∀ t j, (s t j).natAbs ≤ As)
    (he1 : ∀ t j, (e1 t j).natAbs ≤ Ae1)
    (he2 : ∀ j, (e2 j).natAbs ≤ Ae2)
    (hcomp : ∀ j, (comp j).natAbs ≤ Acomp) :
    ((dotNegacyclicCoeff n hn k e r i) + e2 i - (dotNegacyclicCoeff n hn k s e1 i) + comp i).natAbs ≤
      (k * (n * Ae * Ar)) + Ae2 + (k * (n * As * Ae1)) + Acomp := by
  have hbase :
      ((dotNegacyclicCoeff n hn k e r i) + e2 i - (dotNegacyclicCoeff n hn k s e1 i)).natAbs ≤
        (k * (n * Ae * Ar)) + Ae2 + (k * (n * As * Ae1)) :=
    natAbs_residualCoeff_le (n := n) (hn := hn) (k := k) (e := e) (r := r) (s := s) (e1 := e1)
      (e2 := e2) (i := i) (Ae := Ae) (Ar := Ar) (As := As) (Ae1 := Ae1) (Ae2 := Ae2)
      he hr hs he1 he2
  have hcomp' : (comp i).natAbs ≤ Acomp := hcomp i
  have hsum :
      ((dotNegacyclicCoeff n hn k e r i) + e2 i - (dotNegacyclicCoeff n hn k s e1 i) + comp i).natAbs ≤
        ((dotNegacyclicCoeff n hn k e r i) + e2 i - (dotNegacyclicCoeff n hn k s e1 i)).natAbs +
          (comp i).natAbs := by
    simpa [add_assoc, sub_eq_add_neg] using
      (Int.natAbs_add_le
        ((dotNegacyclicCoeff n hn k e r i) + e2 i - (dotNegacyclicCoeff n hn k s e1 i))
        (comp i))
  have :
      ((dotNegacyclicCoeff n hn k e r i) + e2 i - (dotNegacyclicCoeff n hn k s e1 i) + comp i).natAbs ≤
        ((k * (n * Ae * Ar)) + Ae2 + (k * (n * As * Ae1))) + Acomp := by
    exact (le_trans hsum (Nat.add_le_add hbase hcomp'))
  simpa [Nat.add_assoc] using this

end ResidualBounds

end FIPS203
end KEM
end Crypto
end HeytingLean
