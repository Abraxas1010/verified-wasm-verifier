import HeytingLean.IteratedVirtual.SpiralEnergy

/-!
# IteratedVirtual.Bridge.HelixAdelic

Strict-only “local/global” decomposition of the helix embedding, with a **correct** periodicity
statement.

The WIP note `extended_noah` used a `Nat.ceil (2π/step)` periodicity claim; that is generally false
for discrete sampling on `ℕ`. Here we instead prove periodicity under an explicit discretization
assumption:

> `step = 2π / n` for some `n > 0`  ⇒  the XY component is periodic with period `n`.

This matches the intended “XY is local/cyclic; Z is global/iterative” story while staying honest
about discrete periodicity.
-/

namespace HeytingLean
namespace IteratedVirtual
namespace Bridge

noncomputable section

open scoped Real

/-- Parameters for a discrete helix sampling `k ↦ (cos(step*k), sin(step*k), pitch*step*k)`. -/
structure HelixDecomposition where
  step : ℝ
  pitch : ℝ

namespace HelixDecomposition

/-- XY “local” component at iteration `k`. -/
def xy (h : HelixDecomposition) (k : Nat) : ℝ × ℝ :=
  (Real.cos (h.step * (k : ℝ)), Real.sin (h.step * (k : ℝ)))

/-- Z “global” component at iteration `k`. -/
def z (h : HelixDecomposition) (k : Nat) : ℝ :=
  h.pitch * h.step * (k : ℝ)

/-- The corresponding 3D point. -/
def point (h : HelixDecomposition) (k : Nat) : Point3R :=
  { x := (h.xy k).1
    y := (h.xy k).2
    z := h.z k }

@[simp] lemma point_x (h : HelixDecomposition) (k : Nat) :
    (h.point k).x = (h.xy k).1 := rfl

@[simp] lemma point_y (h : HelixDecomposition) (k : Nat) :
    (h.point k).y = (h.xy k).2 := rfl

@[simp] lemma point_z (h : HelixDecomposition) (k : Nat) :
    (h.point k).z = h.z k := rfl

/-- If `step = 2π/n` (with `n>0`), the XY component is periodic with period `n`. -/
theorem local_periodic_of_step_eq_two_pi_div (h : HelixDecomposition)
    (n : Nat) (hn : 0 < n) (hstep : h.step = (2 * Real.pi) / (n : ℝ)) :
    ∀ k : Nat, h.xy (k + n) = h.xy k := by
  intro k
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)

  have hstep_mul_n : h.step * (n : ℝ) = 2 * Real.pi := by
    -- `(2π/n) * n = 2π`
    calc
      h.step * (n : ℝ) = ((2 * Real.pi) / (n : ℝ)) * (n : ℝ) := by simp [hstep]
      _ = 2 * Real.pi := by
        field_simp [hn0]

  have harg :
      h.step * ((k + n : Nat) : ℝ) = h.step * (k : ℝ) + 2 * Real.pi := by
    -- expand `(k+n)` and use `hstep_mul_n`
    calc
      h.step * ((k + n : Nat) : ℝ)
          = h.step * ((k : ℝ) + (n : ℝ)) := by
              simp [Nat.cast_add]
      _ = h.step * (k : ℝ) + h.step * (n : ℝ) := by
              simp [mul_add]
      _ = h.step * (k : ℝ) + 2 * Real.pi := by
              simp [hstep_mul_n]

  have harg' : h.step * ((k : ℝ) + (n : ℝ)) = h.step * (k : ℝ) + 2 * Real.pi := by
    simpa [Nat.cast_add] using harg

  -- Use trig periodicity with period `2π`.
  have hcos :
      Real.cos (h.step * ((k : ℝ) + (n : ℝ))) = Real.cos (h.step * (k : ℝ)) := by
    calc
      Real.cos (h.step * ((k : ℝ) + (n : ℝ)))
          = Real.cos (h.step * (k : ℝ) + 2 * Real.pi) := by
              simp [harg']
      _ = Real.cos (h.step * (k : ℝ)) := by
              exact Real.cos_add_two_pi (h.step * (k : ℝ))

  have hsin :
      Real.sin (h.step * ((k : ℝ) + (n : ℝ))) = Real.sin (h.step * (k : ℝ)) := by
    calc
      Real.sin (h.step * ((k : ℝ) + (n : ℝ)))
          = Real.sin (h.step * (k : ℝ) + 2 * Real.pi) := by
              simp [harg']
      _ = Real.sin (h.step * (k : ℝ)) := by
              exact Real.sin_add_two_pi (h.step * (k : ℝ))

  dsimp [xy]
  refine Prod.ext ?_ ?_
  · simpa [Nat.cast_add, mul_add] using hcos
  · simpa [Nat.cast_add, mul_add] using hsin

end HelixDecomposition

end

end Bridge
end IteratedVirtual
end HeytingLean
