import Mathlib.Order.Nucleus
import HeytingLean.MirandaDynamics.FixedPoint.PeriodicNucleus
import HeytingLean.OTM.DynamicsComputation.DynamicalSystem

namespace HeytingLean
namespace OTM
namespace DynamicsComputation

open Set

universe u

variable {X : Type u}

/--
Data needed to upgrade a reachability-style closure into a full `Nucleus`.
`Mathlib.Order.Nucleus` requires inf-preservation and idempotence in addition to extensivity.
-/
structure ReachabilityNucleusWitness (D : DynamicalSystem X) where
  map_inf :
    ∀ U V : Set X,
      D.reachabilityClosure (U ∩ V) = D.reachabilityClosure U ∩ D.reachabilityClosure V
  idempotent :
    ∀ U : Set X, D.reachabilityClosure (D.reachabilityClosure U) = D.reachabilityClosure U

/--
Compatibility condition ensuring reachability closure respects binary meets.
This is the only non-automatic law needed once semigroup/idempotence are proved.
-/
def ReachabilityMeetCompatible (D : DynamicalSystem X) : Prop :=
  ∀ U V : Set X,
    D.reachabilityClosure U ∩ D.reachabilityClosure V ⊆ D.reachabilityClosure (U ∩ V)

theorem reachabilityClosure_map_inf_of_meetCompatible (D : DynamicalSystem X)
    (hmeet : ReachabilityMeetCompatible D) :
    ∀ U V : Set X,
      D.reachabilityClosure (U ∩ V) = D.reachabilityClosure U ∩ D.reachabilityClosure V := by
  intro U V
  apply Set.Subset.antisymm
  · exact D.reachabilityClosure_inter_subset U V
  · exact hmeet U V

def reachabilityWitnessOfMeetCompatible (D : DynamicalSystem X)
    (hmeet : ReachabilityMeetCompatible D) : ReachabilityNucleusWitness D where
  map_inf := reachabilityClosure_map_inf_of_meetCompatible D hmeet
  idempotent := D.reachabilityClosure_idempotent

/-- Build a `Nucleus` from reachability closure once the missing laws are provided. -/
def reachabilityNucleusOfWitness (D : DynamicalSystem X)
    (h : ReachabilityNucleusWitness D) : Nucleus (Set X) where
  toInfHom :=
    { toFun := D.reachabilityClosure
      map_inf' := h.map_inf }
  idempotent' := by
    intro U
    exact (h.idempotent U).le
  le_apply' := by
    intro U
    exact D.subset_reachabilityClosure U

/--
Convenience constructor: if meet-compatibility is provided, all nucleus
requirements are discharged from local dynamics lemmas.
-/
def reachabilityNucleusOfMeetCompatible (D : DynamicalSystem X)
    (hmeet : ReachabilityMeetCompatible D) : Nucleus (Set X) :=
  reachabilityNucleusOfWitness D (reachabilityWitnessOfMeetCompatible D hmeet)

/--
Canonical dynamics-induced nucleus: adjoin equilibrium states.
This yields an always-available, fully proved nucleus without additional assumptions.
-/
def equilibriumNucleus (D : DynamicalSystem X) : Nucleus (Set X) :=
  MirandaDynamics.FixedPoint.unionNucleus (α := X) D.equilibriumSet

theorem equilibriumNucleus_apply (D : DynamicalSystem X) (U : Set X) :
    equilibriumNucleus D U = U ∪ D.equilibriumSet := rfl

theorem equilibriumNucleus_fixed_iff (D : DynamicalSystem X) (U : Set X) :
    equilibriumNucleus D U = U ↔ D.equilibriumSet ⊆ U := by
  simpa [equilibriumNucleus] using
    (MirandaDynamics.FixedPoint.isFixedPoint_unionNucleus_iff (α := X) D.equilibriumSet U)

/-- A small package exposing both the dynamics and its canonical nucleus. -/
structure DynamicsNucleusInstance (X : Type u) where
  system : DynamicalSystem X
  nucleus : Nucleus (Set X)
  nucleus_spec : nucleus = equilibriumNucleus system

def mkEquilibriumInstance (D : DynamicalSystem X) : DynamicsNucleusInstance X where
  system := D
  nucleus := equilibriumNucleus D
  nucleus_spec := rfl

end DynamicsComputation
end OTM
end HeytingLean
