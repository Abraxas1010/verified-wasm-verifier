import HeytingLean.Crypto.Lattice.NTTCorrectness
import HeytingLean.Crypto.Lattice.NTTIterative
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

/-!
# CRT bridge helpers for quadratic factors `X^2 - μ`

This file provides the key quotient-ring rewrite used to connect coefficient-level formulas to the
CRT factor rings appearing in `NTTCorrectness`:

In `K[X]/(X^2 - μ)`, the image of `X` satisfies `X^2 = μ`.

Downstream, this supports rewriting monomials:
- `X^(2k) = μ^k`
- `X^(2k+1) = μ^k * X`

and therefore expressing the image of a length-256 polynomial as a degree-1 remainder
`a0 + a1*X` where `(a0,a1)` are the even/odd evaluations at `μ`.
-/

namespace HeytingLean
namespace Crypto
namespace Lattice
namespace NTTCRTBridge

open scoped BigOperators Polynomial
open Polynomial

open NTTCorrectness

abbrev q : Nat := NTTCorrectness.q
abbrev K : Type := NTTCorrectness.K
abbrev R : Type := NTTCorrectness.R

namespace Quad

theorem x_sq_eq_c (μ : K) :
    let I : Ideal R := quadIdeal μ
    let x : R ⧸ I := Ideal.Quotient.mk I (X : R)
    let c : K →+* (R ⧸ I) := (Ideal.Quotient.mk I).comp C
    x ^ 2 = c μ := by
  classical
  -- Unfold the `let`-bindings in the goal.
  dsimp
  -- The generator `X^2 - C μ` is zero in the quotient, hence `X^2 = C μ`.
  let I : Ideal R := quadIdeal μ
  have hmem : quad μ ∈ I := by
    refine Ideal.subset_span ?_
    simp
  have hzero : Ideal.Quotient.mk I (quad μ) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 hmem
  have hrel :
      Ideal.Quotient.mk I ((X : R) ^ (2 : Nat)) =
        Ideal.Quotient.mk I (C μ) := by
    -- `mk (X^2 - C μ) = 0` implies `mk (X^2) = mk (C μ)`.
    have : Ideal.Quotient.mk I ((X : R) ^ (2 : Nat) - C μ) = 0 := by
      simpa [quad] using hzero
    exact sub_eq_zero.mp this
  -- Convert `mk (X^2)` into `(mk X)^2` and `mk (C μ)` into `((mk).comp C) μ`.
  simpa [pow_two] using hrel

set_option maxHeartbeats 2000000 in
theorem basemulPair_eq_quotient_mul (a0 a1 b0 b1 μ : K) :
    let I : Ideal R := quadIdeal μ
    let mk : R →+* (R ⧸ I) := Ideal.Quotient.mk I
    mk (C a0 + C a1 * X) * mk (C b0 + C b1 * X) =
      mk (C (a0 * b0 + μ * a1 * b1) + C (a0 * b1 + a1 * b0) * X) := by
  classical
  dsimp
  let I : Ideal R := quadIdeal μ
  let mk : R →+* (R ⧸ I) := Ideal.Quotient.mk I
  let x : R ⧸ I := mk (X : R)
  let c : K →+* (R ⧸ I) := mk.comp C
  have hx2 : x ^ 2 = c μ := by
    -- Reuse the existing quotient relation `X^2 = μ`.
    simpa [I, mk, x, c] using (x_sq_eq_c (μ := μ))
  have hx : x * x = c μ := by
    simpa [pow_two] using hx2
  have hqa : mk (C a0 + C a1 * X) = c a0 + c a1 * x := by
    simp [mk, c, x, I]
  have hqb : mk (C b0 + C b1 * X) = c b0 + c b1 * x := by
    simp [mk, c, x, I]
  have hqrhs :
      mk (C (a0 * b0 + μ * a1 * b1) + C (a0 * b1 + a1 * b0) * X)
        = c (a0 * b0 + μ * a1 * b1) + c (a0 * b1 + a1 * b0) * x := by
    simp [mk, c, x, I]
  -- Expand in the quotient ring and rewrite `x^2 = μ`.
  calc
    mk (C a0 + C a1 * X) * mk (C b0 + C b1 * X)
        = (c a0 + c a1 * x) * (c b0 + c b1 * x) := by simp [hqa, hqb]
    _ = (c a0 * c b0) + (c a0 * c b1 + c a1 * c b0) * x + (c a1 * c b1) * (x * x) := by
          ring
    _ = (c a0 * c b0) + (c a0 * c b1 + c a1 * c b0) * x + (c a1 * c b1) * (c μ) := by
          simp [hx]
    _ = c (a0 * b0 + μ * a1 * b1) + c (a0 * b1 + a1 * b0) * x := by
          -- Push `c` through and use commutativity to match the normal form.
          simp [c, map_add, map_mul]
          ring
    _ = mk (C (a0 * b0 + μ * a1 * b1) + C (a0 * b1 + a1 * b0) * X) := by
          simpa [hqrhs] using hqrhs.symm

end Quad

end NTTCRTBridge
end Lattice
end Crypto
end HeytingLean
