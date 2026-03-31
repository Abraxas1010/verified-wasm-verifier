import HeytingLean.Topology.Knot.BracketMathlibReidemeisterR1
import HeytingLean.Topology.Knot.JonesMathlib

/-!
# Knot theory: Jones normalisation laws (Mathlib proof layer)

This module proves that the Mathlib-layer Jones normalisation cancels the Reidemeister-I scaling
of the Mathlib-layer Kauffman bracket.
-/

namespace HeytingLean
namespace Topology
namespace Knot

namespace Kauffman

open scoped LaurentPolynomial
open Reidemeister

noncomputable section

private theorem writheML_push_pos (sign : Array CurlKind) :
    writheML (sign.push .pos) = writheML sign + 1 := by
  simp [writheML, Array.toList_push, List.foldl_append]

private theorem writheML_push_neg (sign : Array CurlKind) :
    writheML (sign.push .neg) = writheML sign - 1 := by
  simp [writheML, Array.toList_push, List.foldl_append, Int.sub_eq_add_neg]

private theorem neg_normCoeffML_succ (w : Int) : -(normCoeffML (w + 1)) = normCoeffML w := by
  unfold normCoeffML
  rcases Int.emod_two_eq_zero_or_one w with hw | hw
  · have hw' : (w + 1) % 2 = 1 := by
      calc
        (w + 1) % 2 = (w % 2 + 1 % 2) % 2 := by
          exact Int.add_emod w 1 2
        _ = 1 := by simp [hw]
    simp [hw, hw']
  · have hw' : (w + 1) % 2 = 0 := by
      calc
        (w + 1) % 2 = (w % 2 + 1 % 2) % 2 := by
          exact Int.add_emod w 1 2
        _ = 0 := by simp [hw]
    simp [hw, hw']

private theorem normFactorML_mul_r1_pos (w : Int) :
    normFactorML (w + 1) * (-(AML ^ 3 : PolyML)) = normFactorML w := by
  have hA3 : (AML ^ 3 : PolyML) = LaurentPolynomial.T 3 := by
    simp [AML, LaurentPolynomial.T_pow]
  have hT :
      (LaurentPolynomial.T ((-3 : Int) * (w + 1)) : PolyML) * LaurentPolynomial.T 3 =
        LaurentPolynomial.T ((-3 : Int) * w) := by
    have hexp : ((-3 : Int) * (w + 1)) + 3 = (-3 : Int) * w := by
      calc
        ((-3 : Int) * (w + 1)) + 3
            = ((-3 : Int) * w + (-3 : Int) * 1) + 3 := by simp [mul_add]
        _ = (-3 : Int) * w + ((-3 : Int) * 1 + 3) := by
            exact add_assoc ((-3 : Int) * w) ((-3 : Int) * 1) 3
        _ = (-3 : Int) * w := by simp
    calc
      (LaurentPolynomial.T ((-3 : Int) * (w + 1)) : PolyML) * LaurentPolynomial.T 3
          =
          LaurentPolynomial.T (((-3 : Int) * (w + 1)) + 3) := by
            exact (LaurentPolynomial.T_add (R := ℤ) ((-3 : Int) * (w + 1)) 3).symm
      _ = LaurentPolynomial.T ((-3 : Int) * w) := by
            exact congrArg (fun z : Int => (LaurentPolynomial.T z : PolyML)) hexp
  have hCoeff0 : (-(normCoeffML (w + 1) : PolyML)) = (normCoeffML w : PolyML) := by
    have h :=
      congrArg (fun z : ℤ => (z : PolyML)) (neg_normCoeffML_succ (w := w))
    have h' := h
    simp at h'
    exact h'
  unfold normFactorML
  calc
    ((normCoeffML (w + 1) : PolyML) * LaurentPolynomial.T ((-3 : Int) * (w + 1))) *
        (-(AML ^ 3 : PolyML))
        = ((normCoeffML (w + 1) : PolyML) * LaurentPolynomial.T ((-3 : Int) * (w + 1))) *
            (-(LaurentPolynomial.T 3 : PolyML)) := by
          rw [hA3]
    _ = -(((normCoeffML (w + 1) : PolyML) * LaurentPolynomial.T ((-3 : Int) * (w + 1))) *
            LaurentPolynomial.T 3) := by
          rw [mul_neg]
    _ =
        -((normCoeffML (w + 1) : PolyML) *
          (LaurentPolynomial.T ((-3 : Int) * (w + 1)) * LaurentPolynomial.T 3)) := by
          rw [mul_assoc]
    _ =
        -((normCoeffML (w + 1) : PolyML) * LaurentPolynomial.T ((-3 : Int) * w)) := by
          rw [hT]
    _ = (normCoeffML w : PolyML) * LaurentPolynomial.T ((-3 : Int) * w) := by
          rw [← neg_mul]
          rw [hCoeff0]

private theorem normFactorML_mul_r1_neg (w : Int) :
    normFactorML (w - 1) * (-(AinvML ^ 3 : PolyML)) = normFactorML w := by
  have hA3 : (AinvML ^ 3 : PolyML) = LaurentPolynomial.T (-3) := by
    simp [AinvML, LaurentPolynomial.T_pow]
  have hT :
      (LaurentPolynomial.T ((-3 : Int) * (w - 1)) : PolyML) * LaurentPolynomial.T (-3) =
        LaurentPolynomial.T ((-3 : Int) * w) := by
    have hexp : ((-3 : Int) * (w - 1)) + (-3) = (-3 : Int) * w := by
      calc
        ((-3 : Int) * (w - 1)) + (-3)
            = ((-3 : Int) * w - (-3 : Int) * 1) + (-3) := by simp [mul_sub]
        _ = ((-3 : Int) * w + 3) + (-3) := by simp
        _ = (-3 : Int) * w := by simp [add_assoc]
    calc
      (LaurentPolynomial.T ((-3 : Int) * (w - 1)) : PolyML) * LaurentPolynomial.T (-3)
          =
          LaurentPolynomial.T (((-3 : Int) * (w - 1)) + (-3)) := by
            exact (LaurentPolynomial.T_add (R := ℤ) ((-3 : Int) * (w - 1)) (-3)).symm
      _ = LaurentPolynomial.T ((-3 : Int) * w) := by
            exact congrArg (fun z : Int => (LaurentPolynomial.T z : PolyML)) hexp
  have hCoeffZ : -(normCoeffML (w - 1)) = normCoeffML w := by
    -- `neg_normCoeffML_succ (w := w-1)` gives `-(normCoeffML w) = normCoeffML (w-1)`.
    have hBase : -(normCoeffML w) = normCoeffML (w - 1) := by
      have h := neg_normCoeffML_succ (w := w - 1)
      simp [sub_add_cancel] at h
      exact h
    have h' := congrArg (fun z : ℤ => -z) hBase.symm
    simp [neg_neg] at h'
    exact h'
  have hCoeff0 : (-(normCoeffML (w - 1) : PolyML)) = (normCoeffML w : PolyML) := by
    have h := congrArg (fun z : ℤ => (z : PolyML)) hCoeffZ
    have h' := h
    simp at h'
    exact h'
  unfold normFactorML
  calc
    ((normCoeffML (w - 1) : PolyML) * LaurentPolynomial.T ((-3 : Int) * (w - 1))) *
        (-(AinvML ^ 3 : PolyML))
        = ((normCoeffML (w - 1) : PolyML) * LaurentPolynomial.T ((-3 : Int) * (w - 1))) *
            (-(LaurentPolynomial.T (-3) : PolyML)) := by
          rw [hA3]
    _ = -(((normCoeffML (w - 1) : PolyML) * LaurentPolynomial.T ((-3 : Int) * (w - 1))) *
            LaurentPolynomial.T (-3)) := by
          rw [mul_neg]
    _ =
        -((normCoeffML (w - 1) : PolyML) *
          (LaurentPolynomial.T ((-3 : Int) * (w - 1)) * LaurentPolynomial.T (-3))) := by
          rw [mul_assoc]
    _ =
        -((normCoeffML (w - 1) : PolyML) * LaurentPolynomial.T ((-3 : Int) * w)) := by
          rw [hT]
    _ = (normCoeffML w : PolyML) * LaurentPolynomial.T ((-3 : Int) * w) := by
          rw [← neg_mul]
          rw [hCoeff0]

theorem normalizedBracketML_r1Add_pos
    {g g' : PDGraph} {x : Nat} {sign : Array CurlKind}
    (hs : sign.size = g.n)
    (hs' : (sign.push .pos).size = g'.n)
    (h : Reidemeister.r1Add g x .pos = .ok g') :
    normalizedBracketML g' (sign.push .pos) = normalizedBracketML g sign := by
  -- Reduce to a pointwise identity over `bracketGraphML g`.
  simp [normalizedBracketML, hs, hs', writheML_push_pos]
  rw [bracketGraphML_r1Add_pos (g := g) (g' := g') (x := x) (h := h)]
  cases hb : bracketGraphML g with
  | error e =>
      simp
  | ok b =>
      -- Reduce the `Except` bind to a ring identity and cancel the Reidemeister‑I scaling.
      simp
      -- Rewrite the outer negation into a product by `-(AML ^ 3 : PolyML)`.
      rw [← mul_neg]
      rw [← neg_mul]
      rw [← mul_assoc]
      rw [normFactorML_mul_r1_pos (w := writheML sign)]

theorem normalizedBracketML_r1Add_neg
    {g g' : PDGraph} {x : Nat} {sign : Array CurlKind}
    (hs : sign.size = g.n)
    (hs' : (sign.push .neg).size = g'.n)
    (h : Reidemeister.r1Add g x .neg = .ok g') :
    normalizedBracketML g' (sign.push .neg) = normalizedBracketML g sign := by
  simp [normalizedBracketML, hs, hs', writheML_push_neg]
  rw [bracketGraphML_r1Add_neg (g := g) (g' := g') (x := x) (h := h)]
  cases hb : bracketGraphML g with
  | error e =>
      simp
  | ok b =>
      simp
      rw [← mul_neg]
      rw [← neg_mul]
      rw [← mul_assoc]
      rw [normFactorML_mul_r1_neg (w := writheML sign)]

end

end Kauffman

end Knot
end Topology
end HeytingLean
