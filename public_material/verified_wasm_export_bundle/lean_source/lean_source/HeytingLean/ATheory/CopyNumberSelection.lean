import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
/-
# CopyNumberSelection: copy number, Assembly functional, selection predicate

This module defines:
* a generic copy-number observable on a finite set of objects;
* a simple tail model as a function of assembly index;
* a scalar `Assembly` functional combining index and copy number;
* a selection predicate that flags high-index, high-abundance objects.

The quantitative laws are intentionally lightweight. Later phases can refine
the null model and Assembly functional without changing the basic interface.
-/

namespace HeytingLean
namespace ATheory

universe u

/-- Copy number and (optionally) a discrete "weight" for objects of type `V`.

Both fields are natural-valued to keep the initial integration simple and
fully constructive; later phases can lift these to real or extended-real
types if needed. -/
structure CopyNumber (V : Type u) where
  /-- Raw counts for each object. -/
  n : V → Nat
  /-- A secondary weight or normalized proxy (e.g. coarse-grained copy number). -/
  μ : V → Nat

variable {V : Type u}

/-- A schematic tail model for observing an object with assembly index `θ`.
Here we record a simple decreasing function `θ ↦ 1 / (θ + 1)` in the reals,
which can be refined later without changing the call sites. -/
noncomputable def nullTail (θ : Nat) : ℝ :=
  1 / (θ.succ : ℝ)

/-- Assembly functional combining assembly index and copy number. For an object
`v` with index `idx v` and discrete weight `μ v`, we define

* `Assembly idx μ v = (μ v) * (idx v + 1)`

This is a simple, well-typed real-valued combination that is monotone in
both arguments. -/
noncomputable def Assembly (idx : V → Nat) (μ : V → Nat) (v : V) : ℝ :=
  (μ v : ℝ) * (idx v + 1 : ℝ)

namespace Assembly

variable (idx : V → Nat) (μ : V → Nat)

/-- For fixed index, the Assembly score is monotone with respect to `μ`. -/
lemma monotone_in_mu {v : V} {μ₁ μ₂ : V → Nat}
    (hμ : μ₁ v ≤ μ₂ v) :
    Assembly idx μ₁ v ≤ Assembly idx μ₂ v := by
  unfold Assembly
  have hcoe : (μ₁ v : ℝ) ≤ (μ₂ v : ℝ) := by exact_mod_cast hμ
  have hden : 0 ≤ (idx v + 1 : ℝ) := by
    exact_mod_cast (Nat.zero_le (idx v + 1))
  exact mul_le_mul_of_nonneg_right hcoe hden

/-- For fixed `μ`, the Assembly score is monotone with respect to the index. -/
lemma monotone_in_idx {v : V} {idx₁ idx₂ : V → Nat}
    (hidx : idx₁ v ≤ idx₂ v) :
    Assembly idx₁ μ v ≤ Assembly idx₂ μ v := by
  unfold Assembly
  have hμnonneg : 0 ≤ (μ v : ℝ) := by
    exact_mod_cast (Nat.zero_le (μ v))
  have hden : (idx₁ v + 1 : ℝ) ≤ (idx₂ v + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hidx
  exact mul_le_mul_of_nonneg_left hden hμnonneg

end Assembly

/-- Selection predicate: in a finite set `vset`, there exists at least one
object whose index is at least `Θ` and whose weight is at least `τ`. -/
def selected (Θ : Nat) (τ : Nat) (vset : Finset V)
    (idx : V → Nat) (μ : V → Nat) : Prop :=
  ∃ v ∈ vset, idx v ≥ Θ ∧ μ v ≥ τ

namespace selected

variable {Θ Θ' : Nat} {τ τ' : Nat} {vset : Finset V}
variable {idx : V → Nat} {μ : V → Nat}

/-- Monotonicity of `selected` in the threshold `Θ`: if selection holds at a
higher threshold, it also holds at any lower threshold. -/
lemma mono_in_Theta (hΘ : Θ' ≤ Θ)
    (hsel : selected Θ τ vset idx μ) :
    selected Θ' τ vset idx μ := by
  rcases hsel with ⟨v, hvset, hidx, hμ⟩
  refine ⟨v, hvset, ?_, hμ⟩
  exact le_trans hΘ hidx

/-- Monotonicity of `selected` in the threshold `τ`: if selection holds at a
higher abundance threshold, it also holds at any lower threshold. -/
lemma mono_in_tau (hτ : τ' ≤ τ)
    (hsel : selected Θ τ vset idx μ) :
    selected Θ τ' vset idx μ := by
  rcases hsel with ⟨v, hvset, hidx, hμ⟩
  refine ⟨v, hvset, hidx, ?_⟩
  exact le_trans hτ hμ

end selected

/-- Ensemble-level Assembly quantity combining assembly index and copy numbers
over a finite set `vset`. This follows the schematic pattern from the AT
literature, using a simple exponential weight and normalized copy numbers.

When the total copy number `N_T` is zero (e.g., on an empty ensemble), the
value is defined to be `0`. -/
noncomputable def AssemblyEnsemble (idx : V → Nat) (n : V → Nat)
    (vset : Finset V) : ℝ :=
  -- Total copy number as a natural
  let NTn : Nat := vset.sum (fun v => n v)
  -- Guard against the degenerate ensemble: `N_T = 0`
  if NTn = 0 then
    0
  else
    -- Cast the total to `ℝ` once, then reuse it
    let NT : ℝ := (NTn : ℝ)
    vset.sum (fun v =>
      -- NOTE: In `(n v - 1 : ℝ)`, when `n v : ℕ`, the subtraction is first computed in ℕ
      -- (truncating at 0), then coerced to ℝ. Objects with copy number n=0 or n=1
      -- contribute 0 to the sum, which is intentional.
      Real.exp (idx v : ℝ) * ((n v - 1 : ℝ) / NT))

@[simp]
lemma AssemblyEnsemble_empty [DecidableEq V] (idx : V → Nat) (n : V → Nat) :
    AssemblyEnsemble idx n (∅ : Finset V) = 0 := by
  -- By definition `NTn = ∑ v in ∅, n v = 0`
  simp [AssemblyEnsemble]

lemma AssemblyEnsemble_zero_total [DecidableEq V]
    (idx : V → Nat) (n : V → Nat) (vset : Finset V)
    (h : vset.sum (fun v => n v) = 0) :
    AssemblyEnsemble idx n vset = 0 := by
  -- The guard condition triggers when the total copy number is zero
  simp [AssemblyEnsemble, h]

end ATheory
end HeytingLean
