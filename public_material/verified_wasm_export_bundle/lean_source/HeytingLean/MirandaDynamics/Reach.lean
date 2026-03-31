import HeytingLean.ClosingTheLoop.Semantics.RelationalRealizability

/-!
# MirandaDynamics: reachability core (re-export)

Miranda/TKFT-style “dynamical computation” is expressed in this project through a
reachability relation on states.

We reuse the already-mechanized reachability spine from
`HeytingLean.ClosingTheLoop.Semantics.RelationalRealizability` so that:

- “kernel” operators (`K`) and invariants are shared,
- simulation-based realizability transfer is available as-is,
- we avoid duplicating definitions.

This file intentionally contains *no new axioms* and *no new proof gaps*.
-/

namespace HeytingLean
namespace MirandaDynamics

abbrev ReachSystem :=
  HeytingLean.ClosingTheLoop.Semantics.ReachSystem

namespace ReachSystem

abbrev K :=
  HeytingLean.ClosingTheLoop.Semantics.ReachSystem.K

abbrev IsInvariant :=
  HeytingLean.ClosingTheLoop.Semantics.ReachSystem.IsInvariant

abbrev kernel :=
  HeytingLean.ClosingTheLoop.Semantics.ReachSystem.kernel

end ReachSystem

namespace Realizability

abbrev Simulation {S₁ S₂ : ReachSystem} (R : S₁.State → S₂.State → Prop) : Prop :=
  HeytingLean.ClosingTheLoop.Semantics.Realizability.Simulation (S₁ := S₁) (S₂ := S₂) R

abbrev Realizable {S₁ S₂ : ReachSystem} (R : S₁.State → S₂.State → Prop) (Q : Set S₂.State) :
    Set S₁.State :=
  HeytingLean.ClosingTheLoop.Semantics.Realizability.Realizable (S₁ := S₁) (S₂ := S₂) R Q

abbrev realizable_invariant_of_simulation {S₁ S₂ : ReachSystem} {R : S₁.State → S₂.State → Prop} :
    Simulation (S₁ := S₁) (S₂ := S₂) R →
      ∀ {Q : Set S₂.State},
        ReachSystem.IsInvariant (S := S₂) Q →
          ReachSystem.IsInvariant (S := S₁) (Realizable (S₁ := S₁) (S₂ := S₂) R Q) :=
  HeytingLean.ClosingTheLoop.Semantics.Realizability.realizable_invariant_of_simulation

end Realizability

end MirandaDynamics
end HeytingLean
