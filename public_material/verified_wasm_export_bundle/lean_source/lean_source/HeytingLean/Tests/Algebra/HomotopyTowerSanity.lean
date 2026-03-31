import Mathlib.CategoryTheory.Category.Quiv
import HeytingLean.Algebra.HomotopyTower
import HeytingLean.Genesis.Stabilization

namespace HeytingLean.Tests.Algebra

open CategoryTheory
open HeytingLean.Algebra.HomotopyTower

/-- Identity ratchet step used to instantiate the tower infrastructure on a concrete nucleus. -/
noncomputable def idRatchetStep : HeytingLean.PerspectivalPlenum.RatchetStep (Set Nat) where
  step := id
  extensive := by
    intro J
    exact le_rfl
  monotone := by
    intro J K hJK
    exact hJK
  idempotent := by
    intro J
    rfl

/-- Concrete ratchet tower whose stabilized layer is the Genesis collapse nucleus. -/
noncomputable def collapseTower : HeytingLean.PerspectivalPlenum.RatchetTower (Set Nat) where
  base := HeytingLean.Genesis.collapseNucleus
  step := idRatchetStep

noncomputable def collapseTowerFiniteImage :
    FiniteImage (ofRatchetTower collapseTower) :=
  ratchetTower_finiteImage collapseTower

/-- A trivial observable, enough to test the spectral bridge interface. -/
def emptyObservable (_J : Nucleus (Set Nat)) : Nat := 1

example : TowerStabilizes (ofRatchetTower collapseTower) 1 :=
  ratchetTower_stabilizes_at_one collapseTower

example :
    HeytingLean.Algebra.SpectralSequence.SpectralConvergesAt
      (stageProfile emptyObservable (ofRatchetTower collapseTower)) 1 :=
  ratchetTower_stageProfile_spectralConverges_at_one emptyObservable collapseTower

example : (∅ : Set Nat) ∈ stableBoundary (ofRatchetTower collapseTower) collapseTowerFiniteImage := by
  change limitNucleus (ofRatchetTower collapseTower) collapseTowerFiniteImage (∅ : Set Nat) ≠ ∅
  rw [ratchetTower_limitNucleus_eq_layer_one (R := collapseTower) collapseTowerFiniteImage]
  simp [collapseTower, idRatchetStep, HeytingLean.Genesis.collapseNucleus_apply]

example :
    HeytingLean.HossenfelderNoGo.HeytingBoundary.boundaryGap
        (stableBoundaryNucleus (ofRatchetTower collapseTower) collapseTowerFiniteImage)
        (∅ : Set Nat) ≠ ∅ := by
  apply stableBoundaryGap_nonempty_of_moved
  exact (show (∅ : Set Nat) ∈ stableBoundary (ofRatchetTower collapseTower) collapseTowerFiniteImage from by
    change limitNucleus (ofRatchetTower collapseTower) collapseTowerFiniteImage (∅ : Set Nat) ≠ ∅
    rw [ratchetTower_limitNucleus_eq_layer_one (R := collapseTower) collapseTowerFiniteImage]
    simp [collapseTower, idRatchetStep, HeytingLean.Genesis.collapseNucleus_apply])

/-- Trivial quiver data attached to the stabilized fixed-point carriers. -/
noncomputable def trivialTransportQuiver :
    StableTransportQuiver (ofRatchetTower collapseTower) collapseTowerFiniteImage where
  Obj := fun _ => Discrete PUnit
  instQuiver := fun _ => by infer_instance
  drop := fun _ => 𝟭q _

noncomputable example : Groupoid (stableGroupoidLimit trivialTransportQuiver) := inferInstance

end HeytingLean.Tests.Algebra
