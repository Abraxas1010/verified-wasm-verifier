import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import HeytingLean.Computation.YWitness.Multiway

namespace HeytingLean.Computation.YWitness

open HeytingLean.LoF

/-- The finite productive frontier at a given depth keeps the current term and all one-step
successors visible for normalization. -/
def productiveFrontierAtDepth (depth : Nat) (seed : Comb) : Finset Comb :=
  insert (yProductiveSequence seed depth)
    ((Comb.stepEdges (yProductiveSequence seed depth)).image Prod.snd)

/-- Finite path count for the retained productive frontier. -/
def pathCountAtDepth (depth : Nat) (seed : Comb) : Nat :=
  (productiveFrontierAtDepth depth seed).card

/-- Uniform mass of a single retained frontier point at the chosen depth. -/
def normalizedWeightAtDepth (depth : Nat) (seed : Comb) : Rat :=
  1 / (pathCountAtDepth depth seed : Rat)

theorem productiveFrontierAtDepth_self_mem (depth : Nat) (seed : Comb) :
    yProductiveSequence seed depth ∈ productiveFrontierAtDepth depth seed := by
  simp [productiveFrontierAtDepth]

theorem pathCountAtDepth_pos (depth : Nat) (seed : Comb) :
    0 < pathCountAtDepth depth seed := by
  unfold pathCountAtDepth
  exact Finset.card_pos.mpr ⟨yProductiveSequence seed depth, productiveFrontierAtDepth_self_mem depth seed⟩

theorem normalizedWeight_total_mass_one (depth : Nat) (seed : Comb) :
    (pathCountAtDepth depth seed : Rat) * normalizedWeightAtDepth depth seed = 1 := by
  have hpos : 0 < pathCountAtDepth depth seed := pathCountAtDepth_pos depth seed
  have hneNat : pathCountAtDepth depth seed ≠ 0 := Nat.ne_of_gt hpos
  have hneRat : (pathCountAtDepth depth seed : Rat) ≠ 0 := by
    exact_mod_cast hneNat
  calc
    (pathCountAtDepth depth seed : Rat) * normalizedWeightAtDepth depth seed
        = (pathCountAtDepth depth seed : Rat) * (1 / (pathCountAtDepth depth seed : Rat)) := by
            rfl
    _ = 1 := by
      field_simp [hneRat]

/-- The finite productive frontier always assigns strictly positive mass to each retained point. -/
theorem finite_productive_paths_have_positive_weight (depth : Nat) (seed : Comb) :
    0 < normalizedWeightAtDepth depth seed := by
  have hpos : (0 : Rat) < (pathCountAtDepth depth seed : Rat) := by
    exact_mod_cast pathCountAtDepth_pos depth seed
  simpa [normalizedWeightAtDepth] using one_div_pos.mpr hpos

end HeytingLean.Computation.YWitness
