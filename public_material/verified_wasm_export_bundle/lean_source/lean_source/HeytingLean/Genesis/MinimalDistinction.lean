import HeytingLean.Genesis.LatticeNucleusBridge
import Mathlib.Order.Atoms

/-!
# Genesis.MinimalDistinction

Phase-4 minimal distinction lane on emergent regions.
-/

namespace HeytingLean.Genesis

open CoGame

/-- Phase-I pole (anchored region). -/
def phasePoleI : EmergentRegion := ({anchorClass} : Set EmergentClass)

/-- Phase-J pole (anchored region with one additional witness class). -/
def phasePoleJ : EmergentRegion :=
  ({anchorClass, toEmergentClass CoGame.Life} : Set EmergentClass)

/-- Minimal distinction as the meet of phase poles. -/
def minimalDistinction : EmergentRegion := phasePoleI ⊓ phasePoleJ

@[simp] theorem minimalDistinction_def :
    minimalDistinction = phasePoleI ⊓ phasePoleJ := rfl

@[simp] theorem minimalDistinction_eq_singleton :
    minimalDistinction = ({anchorClass} : EmergentRegion) := by
  ext x
  simp [minimalDistinction, phasePoleI, phasePoleJ]

theorem bot_lt_minimalDistinction : (⊥ : EmergentRegion) < minimalDistinction := by
  rw [bot_lt_iff_ne_bot]
  intro hbot
  have hmem : anchorClass ∈ minimalDistinction := by
    simp [minimalDistinction, phasePoleI, phasePoleJ]
  have : anchorClass ∈ (⊥ : EmergentRegion) := hbot ▸ hmem
  simp at this

theorem minimalDistinction_atom : IsAtom minimalDistinction := by
  rw [minimalDistinction_eq_singleton]
  exact (Set.isAtom_singleton anchorClass : IsAtom ({anchorClass} : EmergentRegion))

/-- Region-level inclusion alias for explicit phase-4 order statements. -/
def regionLe (U V : EmergentRegion) : Prop := U ⊆ V

/-- Nucleus extensivity as the phase-4 floor alignment law (`x ≤ R x`). -/
theorem nucleus_extensive_floor (U : EmergentRegion) : regionLe U (regionNucleus U) :=
  Nucleus.le_apply (n := regionNucleus) (x := U)

end HeytingLean.Genesis
