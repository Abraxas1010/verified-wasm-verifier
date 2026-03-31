import Mathlib.Tactic

/-!
# Langmuir adsorption (single-site equilibrium identity)

This is a Lean 4, HeytingLean-native formalization of the standard algebraic identity behind the
Langmuir isotherm at equilibrium:

  theta = K*P / (1 + K*P)

We model the derivation purely algebraically over a commutative field; analytic/physical assumptions
(positivity, units, etc.) can be layered later.

This mirrors the "Langmuir single site" proof pattern described in arXiv:2210.12150, but is written
directly in Lean 4.
-/

namespace HeytingLean
namespace Chem
namespace Theories
namespace Adsorption

variable {K : Type} [Field K]

theorem langmuir_single_site
    (P k_ad k_d A S : K)
    (hreaction : k_ad * P * S = k_d * A)
    (hS : S ≠ 0)
    (hk_d : k_d ≠ 0) :
    A / (S + A) = (k_ad / k_d) * P / (1 + (k_ad / k_d) * P) := by
  -- Solve the reaction equation for A.
  have hA : A = (k_ad / k_d) * P * S := by
    -- Multiply the reaction equation by `k_d⁻¹` on the left to cancel `k_d` on the RHS.
    have h' := congrArg (fun t : K => k_d⁻¹ * t) hreaction
    have h'' : k_d⁻¹ * (k_ad * P * S) = A := by
      -- `k_d⁻¹ * (k_d * A) = A` uses `hk_d`.
      simpa [mul_assoc, hk_d] using h'
    -- Normalize into `A = (k_ad / k_d) * P * S`.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h''.symm

  -- Substitute A and cancel the common factor S.
  -- Let b := (k_ad / k_d) * P.
  set b : K := (k_ad / k_d) * P
  calc
    A / (S + A) = (b * S) / (S + b * S) := by
      -- unfold b and rewrite using hA
      simp [b, hA]
    _ = (S * b) / (S * (1 + b)) := by
      -- Commute `b * S` into `S * b`, and factor `S` out of `S + S*b`.
      have hb : b * S = S * b := by simp [mul_comm]
      -- Rewrite into a common normal form.
      -- `simp` expands `S * (1 + b)` into `S + S*b`.
      simp [hb, mul_add, add_comm]
    _ = b / (1 + b) := by
      -- Cancel S (nonzero).
      simp [mul_div_mul_left, hS]
    _ = (k_ad / k_d) * P / (1 + (k_ad / k_d) * P) := by
      simp [b]

end Adsorption
end Theories
end Chem
end HeytingLean
