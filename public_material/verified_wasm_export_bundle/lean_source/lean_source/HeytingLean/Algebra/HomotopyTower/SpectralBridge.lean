import HeytingLean.Algebra.HomotopyTower.Stabilization
import HeytingLean.Algebra.SpectralSequence.RatchetConvergence

namespace HeytingLean
namespace Algebra
namespace HomotopyTower

universe u

open HeytingLean.Algebra.SpectralSequence

variable {α : Type u} [Order.Frame α]

/-- Any numeric observable on nuclei yields a stagewise profile on a tower. -/
def stageProfile (measure : Nucleus α → Nat) (T : NucleusTower (α := α)) : Nat → Nat :=
  fun n => measure (T.level n)

/-- Eventual constancy of the tower forces eventual constancy of any observable profile. -/
theorem stageProfile_stabilizes
    (measure : Nucleus α → Nat) {T : NucleusTower (α := α)} {N : Nat}
    (hT : TowerStabilizes T N) :
    SpectralSequence.Stabilizes (stageProfile measure T) N := by
  intro n hn
  simp [stageProfile, hT n hn]

/-- The observable profile therefore converges in the existing spectral interface. -/
theorem stageProfile_spectralConverges
    (measure : Nucleus α → Nat) {T : NucleusTower (α := α)} {N : Nat}
    (hT : TowerStabilizes T N) :
    SpectralSequence.SpectralConvergesAt (stageProfile measure T) N := by
  exact (SpectralSequence.spectralConvergesAt_iff_stabilizes (stageProfile measure T) N).2
    (stageProfile_stabilizes measure hT)

/-- A ratchet tower stabilizes after the first nontrivial stage. -/
theorem ratchetTower_stabilizes_at_one (R : PerspectivalPlenum.RatchetTower α) :
    TowerStabilizes (ofRatchetTower R) 1 := by
  intro n hn
  rcases Nat.exists_eq_add_of_le hn with ⟨k, hk⟩
  subst hk
  simpa [ofRatchetTower, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    R.layer_stabilizes k

/-- The image of a ratchet tower has at most the base layer and the stabilized layer. -/
theorem ratchetTower_finiteImage (R : PerspectivalPlenum.RatchetTower α) :
    FiniteImage (ofRatchetTower R) := by
  rw [FiniteImage]
  let S : Set (Nucleus α) := {R.base, R.layer 1}
  have hSfin : S.Finite := by
    simp [S]
  refine hSfin.subset ?_
  intro J hJ
  rcases hJ with ⟨n, rfl⟩
  cases n with
  | zero =>
      simp [S, ofRatchetTower]
  | succ k =>
      right
      simpa [S, ofRatchetTower, PerspectivalPlenum.RatchetTower.layer_succ] using
        R.layer_stabilizes k

/-- The stabilized limit nucleus of a ratchet tower is the first nontrivial layer. -/
theorem ratchetTower_limitNucleus_eq_layer_one
    (R : PerspectivalPlenum.RatchetTower α) (hfin : FiniteImage (ofRatchetTower R)) :
    limitNucleus (ofRatchetTower R) hfin = R.layer 1 := by
  cases hidx : stabilizationIndex (ofRatchetTower R) hfin with
  | zero =>
      rw [limitNucleus, hidx]
      have h :
          (ofRatchetTower R).level 1 = (ofRatchetTower R).level 0 := by
        simpa [hidx] using
          (stabilizationIndex_spec (ofRatchetTower R) hfin 1 (by simp [hidx]))
      simp [ofRatchetTower] at h ⊢
      exact h.symm
  | succ k =>
      rw [limitNucleus, hidx]
      simpa [ofRatchetTower] using R.layer_stabilizes k

/-- Any observable on a ratchet tower converges at page `1` in the spectral interface. -/
theorem ratchetTower_stageProfile_spectralConverges_at_one
    (measure : Nucleus α → Nat) (R : PerspectivalPlenum.RatchetTower α) :
    SpectralSequence.SpectralConvergesAt (stageProfile measure (ofRatchetTower R)) 1 := by
  exact stageProfile_spectralConverges measure (ratchetTower_stabilizes_at_one R)

end HomotopyTower
end Algebra
end HeytingLean
