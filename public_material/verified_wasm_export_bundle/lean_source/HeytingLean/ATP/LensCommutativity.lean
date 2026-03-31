import HeytingLean.ATP.PremiseNucleus

/-!
# Lens Commutativity for ATP Routing

When ATP lenses commute, routing order doesn't matter. This module formalizes
the commutativity condition and proves that closureByFocus-style lenses always
commute (since `P ∨ Q` is commutative and associative).

This mirrors `canonical_lenses_commute_algebraically` from
`HeytingLean.Bridge.NoCoincidence.Nucleus.NucleusDecomposition` but
generalized from `CircuitProp n` to `GoalProp G`.
-/

namespace HeytingLean.ATP

/-- Two lenses commute when their nucleus operators can be applied in either order. -/
def LensCommutes {G : Type*} (R₁ R₂ : PremiseNucleus G) : Prop :=
  R₁.independent R₂

/-- For closureByFocus-style lenses, commutativity is automatic.
Proof pattern: funext + propext + tauto (from NucleusDecomposition.lean:29-52). -/
theorem closureByFocus_lenses_commute {G : Type*}
    (R₁ R₂ : PremiseNucleus G) :
    LensCommutes R₁ R₂ :=
  closureByFocus_premise_nuclei_commute R₁ R₂

end HeytingLean.ATP
