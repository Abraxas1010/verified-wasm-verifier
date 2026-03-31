import HeytingLean.Crypto.Lattice.NoiseMLWE
import Mathlib.Data.Int.Order.Lemmas

/-!
# Centered Binomial Distribution (CBD) — bounded coefficient carrier

This file provides a **spec-first** CBD coefficient carrier aligned with ML-KEM/ML-DSA style noise:

- a CBD coefficient is an integer `x` with `|x| ≤ η`;
- we can cast such coefficients into `ZMod q`;
- with centered coefficient bounds (`coeffBound` uses `ZMod.valMinAbs`), small negative noise remains small.

This is intentionally probability-free: we do not formalize the sampling algorithm or the moments
(`E=0`, `Var=η/2`) in this layer.
-/

namespace HeytingLean
namespace Crypto
namespace Lattice
namespace CBD

/-- CBD parameters (only the bound `η`). -/
structure CBDParams where
  eta : Nat
  hpos : 0 < eta

/-- A CBD sample is an integer bounded in absolute value by `η`. -/
def CBDSample (p : CBDParams) : Type :=
  { x : Int // x.natAbs ≤ p.eta }

theorem cbd_bounded (p : CBDParams) (s : CBDSample p) : s.val.natAbs ≤ p.eta :=
  s.property

/-- A length-`n` CBD polynomial (coefficient function). -/
def CBDPoly (n : Nat) (p : CBDParams) : Type :=
  Fin n → CBDSample p

/-- Cast a CBD coefficient to `ZMod q`. -/
def coeffToZMod {q : Nat} (_p : CBDParams) (x : Int) : ZMod q :=
  (x : ZMod q)

/-- Cast a CBD polynomial to `ZMod q` coefficients. -/
def polyToZMod {n q : Nat} (p : CBDParams) (f : CBDPoly n p) : Fin n → ZMod q :=
  fun i => (f i).val

/-!
## Coefficient bounds in `ZMod q`

If `q > 2η`, then casting an integer `x` with `|x| ≤ η` into `ZMod q` preserves the centered
representative, so `coeffBound` is bounded by `η`.
-/

theorem coeffBound_int_cast_le {q : Nat} [NeZero q] (p : CBDParams) (x : Int)
    (hx : x.natAbs ≤ p.eta) (hq : 2 * p.eta < q) :
    coeffBound (q := q) (x : ZMod q) ≤ p.eta := by
  -- Show `valMinAbs (x : ZMod q) = x` by the `valMinAbs_spec` characterization.
  have hxabs : |x| ≤ (p.eta : ℤ) := by
    have hx' : (x.natAbs : ℤ) ≤ (p.eta : ℤ) := Int.ofNat_le.mpr hx
    -- `Int.abs_eq_natAbs` rewrites `|x|` to the coercion of `x.natAbs`.
    rw [Int.abs_eq_natAbs]
    exact hx'
  have hx2abs : |x * 2| < (q : ℤ) := by
    -- `|x*2| ≤ 2*|x| ≤ 2*eta < q`.
    have hx2le : |x * 2| ≤ (p.eta : ℤ) * 2 := by
      calc
        |x * 2| = |x| * |(2 : ℤ)| := by simp [abs_mul]
        _ = |x| * 2 := by simp
        _ ≤ (p.eta : ℤ) * 2 := by
          exact mul_le_mul_of_nonneg_right hxabs (by norm_num)
    have hq' : ((p.eta : ℤ) * 2) < (q : ℤ) := by
      have hqNat : p.eta * 2 < q := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hq
      exact Int.ofNat_lt.mpr hqNat
    exact lt_of_le_of_lt hx2le hq'
  have hx2Ioc : (x * 2) ∈ Set.Ioc (-(q : ℤ)) (q : ℤ) := by
    -- From `|x*2| < q`, we get `-q < x*2` and `x*2 < q`.
    have : (-(q : ℤ) < x * 2) ∧ (x * 2 < (q : ℤ)) := (abs_lt).1 hx2abs
    exact ⟨this.1, le_of_lt this.2⟩
  have hspec :
      (ZMod.valMinAbs (n := q) (x : ZMod q)) = x := by
    -- Apply `valMinAbs_spec` (mpr direction).
    exact (ZMod.valMinAbs_spec (n := q) (x := (x : ZMod q)) x).2 ⟨by simp, hx2Ioc⟩
  -- Finish by unfolding `coeffBound`.
  simpa [coeffBound, hspec] using hx

/-- Componentwise noise bound for CBD polynomials when `q > 2η`. -/
theorem coeffBound_poly_cast_le {n q : Nat} [NeZero q] (p : CBDParams) (f : CBDPoly n p)
    (hq : 2 * p.eta < q) (i : Fin n) :
    coeffBound (q := q) ((polyToZMod (q := q) p f) i) ≤ p.eta := by
  exact coeffBound_int_cast_le (q := q) (p := p) (x := (f i).val) (f i).property hq

end CBD
end Lattice
end Crypto
end HeytingLean
