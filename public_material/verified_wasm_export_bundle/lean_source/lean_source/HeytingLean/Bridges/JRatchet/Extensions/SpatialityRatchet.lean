import HeytingLean.Bridges.JRatchet.RatchetStepNucleus
import Mathlib.Order.Nucleus

/-!
# SpatialityRatchet

This module provides a point-based interface for ratchet reasoning on `Nucleus α`,
inspired by spatiality criteria for frames of nuclei (Bezhanishvili et al., 2019).
-/

namespace HeytingLean
namespace Bridges
namespace JRatchet
namespace Extensions
namespace SpatialityRatchet

open HeytingLean.PerspectivalPlenum

universe u

variable {α : Type u} [Order.Frame α]

/-- A nuclear point candidate in the frame of nuclei. -/
structure NuclearPoint where
  /-- The nucleus represented by this point. -/
  nucleus : Nucleus α
  /-- Meet-irreducibility witness (point-style condition). -/
  meet_irreducible :
    ∀ J K : Nucleus α,
      nucleus ≤ J ⊔ K → nucleus ≤ J ∨ nucleus ≤ K

/--
Spatiality proxy used in this module: nuclear points separate nuclei.

If every nuclear point below `J` is also below `K`, then `J ≤ K`.
-/
def NucFrameSpatial : Prop :=
  ∀ J K : Nucleus α,
    (∀ p : NuclearPoint (α := α), p.nucleus ≤ J → p.nucleus ≤ K) →
      J ≤ K

/-- Extensionality for ratchet steps by pointwise equality on nuclei. -/
@[ext] theorem RatchetStep_ext {S T : RatchetStep α}
    (h : ∀ J : Nucleus α, S.step J = T.step J) :
    S = T := by
  cases S with
  | mk s se sm si =>
      cases T with
      | mk t te tm ti =>
          have hs : s = t := funext h
          subst hs
          simp

/--
In the spatial setting, pointwise order profiles on nuclear points determine
the whole ratchet step.
-/
theorem ratchetStep_determined_by_points
    (hsp : NucFrameSpatial (α := α))
    (S T : RatchetStep α)
    (hST : ∀ J : Nucleus α, ∀ p : NuclearPoint (α := α),
      p.nucleus ≤ S.step J → p.nucleus ≤ T.step J)
    (hTS : ∀ J : Nucleus α, ∀ p : NuclearPoint (α := α),
      p.nucleus ≤ T.step J → p.nucleus ≤ S.step J) :
    S = T := by
  apply RatchetStep_ext
  intro J
  apply le_antisymm
  · exact hsp (S.step J) (T.step J) (hST J)
  · exact hsp (T.step J) (S.step J) (hTS J)

/-- Point-based fixed-point characterization in the spatial setting. -/
theorem spatial_ratchetFixed_iff_pointwise
    (hsp : NucFrameSpatial (α := α))
    (S : RatchetStep α)
    (J : Nucleus α) :
    isRatchetFixed S J ↔
      ∀ p : NuclearPoint (α := α),
        p.nucleus ≤ S.step J →
        p.nucleus ≤ J := by
  constructor
  · intro hfix p hp
    change S.step J = J at hfix
    simpa [hfix] using hp
  · intro hpoint
    have hExt : J ≤ S.step J := S.extensive J
    have hLe : S.step J ≤ J := hsp (S.step J) J hpoint
    exact le_antisymm hLe hExt

end SpatialityRatchet
end Extensions
end JRatchet
end Bridges
end HeytingLean
