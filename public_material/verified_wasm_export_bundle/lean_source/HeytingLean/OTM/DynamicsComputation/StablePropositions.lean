import Mathlib.Order.Sublocale
import HeytingLean.OTM.DynamicsComputation.NucleusFromDynamics

namespace HeytingLean
namespace OTM
namespace DynamicsComputation

universe u

open Set

variable {X : Type u} (J : Nucleus (Set X))

/-- The type of `J`-closed propositions (stable propositions). -/
abbrev StableProp : Type u := J.toSublocale

theorem mem_stable_iff_fixed (U : Set X) :
    U ∈ J.toSublocale ↔ J U = U := by
  constructor
  · intro hU
    rcases hU with ⟨V, hV⟩
    calc
      J U = J (J V) := by simp [hV]
      _ = J V := J.idempotent _
      _ = U := hV
  · intro hU
    exact ⟨U, hU⟩

/-- Canonical "close then view as stable" map. -/
def closeAsStable (U : Set X) : StableProp J :=
  ⟨J U, by exact ⟨U, rfl⟩⟩

@[simp] theorem closeAsStable_val (U : Set X) :
    ((closeAsStable (J := J) U : StableProp J) : Set X) = J U := rfl

@[simp] theorem closeAsStable_idem (U : Set X) :
    closeAsStable (J := J) (J U) = closeAsStable (J := J) U := by
  apply Subtype.ext
  simp [closeAsStable, J.idempotent]

/--
Closed propositions in `toSublocale` are equivalent to fixed points of `J`.
This provides a simple bridge for transporting statements between both views.
-/
def stablePropEquivFixed :
    StableProp J ≃ {U : Set X // J U = U} where
  toFun U := ⟨U.1, (mem_stable_iff_fixed (J := J) U.1).1 U.2⟩
  invFun U := ⟨U.1, (mem_stable_iff_fixed (J := J) U.1).2 U.2⟩
  left_inv U := by
    apply Subtype.ext
    rfl
  right_inv U := by
    apply Subtype.ext
    rfl

/--
Canonical lattice-emergence theorem surface for the stable-proposition view:
stable propositions coincide with nucleus fixed points, and closing is idempotent.
-/
theorem lattice_emergence_theorem :
    Nonempty (StableProp J ≃ {U : Set X // J U = U}) ∧
      (∀ U : Set X, ((closeAsStable (J := J) U : StableProp J) : Set X) = J U) ∧
      (∀ U : Set X, closeAsStable (J := J) (J U) = closeAsStable (J := J) U) := by
  refine ⟨⟨stablePropEquivFixed (J := J)⟩, ?_, ?_⟩
  · intro U
    exact closeAsStable_val (J := J) U
  · intro U
    exact closeAsStable_idem (J := J) U

end DynamicsComputation
end OTM
end HeytingLean
