import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Basic

/-!
# IteratedVirtual.SpiralEnergy

An intentionally modest “tension minimization” theorem:

We define a nonnegative discrete energy functional that measures deviation from the helix
constraints:
- unit radius in the x/y plane;
- z coordinate equal to `pitch * t`.

Then the helix point has energy `0`, hence minimizes this energy (pointwise, and by summing
over a list of samples).

This avoids heavy calculus-of-variations infrastructure while still giving a *proved* link
between the computed helix embedding and an explicit “tension” objective.
-/

namespace HeytingLean
namespace IteratedVirtual

noncomputable section

structure Point3R where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Point3R

def helix (t : ℝ) (pitch : ℝ := 0.15) : Point3R :=
  { x := Real.cos t
    y := Real.sin t
    z := pitch * t }

/-- “Tension energy” at a parameter value `t`: radial constraint + z-constraint, squared. -/
def tensionEnergyAt (t : ℝ) (pitch : ℝ) (p : Point3R) : ℝ :=
  let rErr := (p.x ^ 2 + p.y ^ 2 - 1)
  let zErr := (p.z - pitch * t)
  rErr ^ 2 + zErr ^ 2

theorem tensionEnergyAt_nonneg (t pitch : ℝ) (p : Point3R) : 0 ≤ tensionEnergyAt t pitch p := by
  dsimp [tensionEnergyAt]
  nlinarith [sq_nonneg (p.x ^ 2 + p.y ^ 2 - 1), sq_nonneg (p.z - pitch * t)]

theorem tensionEnergyAt_helix (t pitch : ℝ) :
    tensionEnergyAt t pitch (helix t pitch) = 0 := by
  dsimp [tensionEnergyAt, helix]
  have hxy : Real.cos t ^ 2 + Real.sin t ^ 2 - 1 = 0 := by
    have := Real.cos_sq_add_sin_sq t
    linarith
  have hz : pitch * t - pitch * t = (0 : ℝ) := by ring
  -- `nlinarith` closes after rewriting with the constraints.
  nlinarith [hxy, hz]

/-- Pointwise minimization: helix achieves the minimal possible energy `0`. -/
theorem helix_minimizes_pointwise (t pitch : ℝ) (p : Point3R) :
    tensionEnergyAt t pitch (helix t pitch) ≤ tensionEnergyAt t pitch p := by
  have hn : 0 ≤ tensionEnergyAt t pitch p := tensionEnergyAt_nonneg t pitch p
  simpa [tensionEnergyAt_helix t pitch] using hn

/-- Energy of a list of samples `(tᵢ, pᵢ)` by summing pointwise energies. -/
def tensionEnergyList (pitch : ℝ) (samples : List (ℝ × Point3R)) : ℝ :=
  (samples.map (fun tp => tensionEnergyAt tp.1 pitch tp.2)).sum

@[simp] theorem tensionEnergyList_cons (pitch : ℝ) (tp : ℝ × Point3R) (rest : List (ℝ × Point3R)) :
    tensionEnergyList pitch (tp :: rest) =
      tensionEnergyAt tp.1 pitch tp.2 + tensionEnergyList pitch rest := by
  simp [tensionEnergyList, List.map_cons, List.sum_cons]

theorem tensionEnergyList_nonneg (pitch : ℝ) (samples : List (ℝ × Point3R)) :
    0 ≤ tensionEnergyList pitch samples := by
  classical
  induction samples with
  | nil =>
      simp [tensionEnergyList]
  | cons tp rest ih =>
      have htp : 0 ≤ tensionEnergyAt tp.1 pitch tp.2 := tensionEnergyAt_nonneg _ _ _
      simpa [tensionEnergyList, List.map_cons, List.sum_cons] using add_nonneg htp ih

theorem tensionEnergyList_helix (pitch : ℝ) (ts : List ℝ) :
    tensionEnergyList pitch (ts.map (fun t => (t, helix t pitch))) = 0 := by
  classical
  induction ts with
  | nil =>
      simp [tensionEnergyList]
  | cons t rest ih =>
      -- Expand at the head and use the induction hypothesis on the tail.
      simp [tensionEnergyList_cons, tensionEnergyAt_helix, ih]

theorem helix_minimizes_list (pitch : ℝ) (ts : List ℝ) (ps : List Point3R) :
    tensionEnergyList pitch (ts.zip ps) ≥
      tensionEnergyList pitch (ts.map (fun t => (t, helix t pitch))) := by
  have hn : 0 ≤ tensionEnergyList pitch (ts.zip ps) := tensionEnergyList_nonneg pitch (ts.zip ps)
  have hz : tensionEnergyList pitch (ts.map (fun t => (t, helix t pitch))) = 0 :=
    tensionEnergyList_helix pitch ts
  linarith [hn, hz]

/-!
## “As k → ∞” (atTop) minimization statement

Since the helix achieves energy `0` at every parameter value, the sequence of energies along
integer samples is identically `0`, hence tends to `0` as `k → ∞`.
-/

theorem tendsto_tensionEnergyAt_helix_atTop (pitch : ℝ) :
    Filter.Tendsto
      (fun k : Nat => tensionEnergyAt (t := (k : ℝ)) pitch (helix (t := (k : ℝ)) pitch))
      Filter.atTop (nhds (0 : ℝ)) := by
  simp [tensionEnergyAt_helix]

end Point3R

end

end IteratedVirtual
end HeytingLean
