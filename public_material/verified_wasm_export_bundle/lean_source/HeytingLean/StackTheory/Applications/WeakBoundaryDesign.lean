import HeytingLean.StackTheory.Collective.CancerAnalogue

namespace HeytingLean.StackTheory.Applications

open HeytingLean.StackTheory

/-- Bennett §6 application: weak boundary conditions are exactly those that preserve a
nonempty restricted collective set. -/
def boundaryIsWeakEnough {Φ : Type*} [DecidableEq Φ] [Fintype Φ]
    {m : ℕ} (v : Vocabulary Φ) (parts : Fin m → VTask v)
    (bc : BoundaryConditions v parts) : Prop :=
  (restrictedCollective v parts bc).Nonempty

/-- Bennett Claim 1.4 application: a weak-enough boundary exposes a genuinely global policy whose
feasible part set is all of `Fin m`, so the boundary does not merely preserve existence; it
preserves unsplintered global feasibility. -/
theorem weak_boundary_exhibits_global_policy
    {Φ : Type*} [DecidableEq Φ] [Fintype Φ]
    {m : ℕ} (v : Vocabulary Φ) (parts : Fin m → VTask v)
    (bc : BoundaryConditions v parts)
    (hWeak : boundaryIsWeakEnough v parts bc) :
    ∃ π ∈ restrictedCollective v parts bc,
      feasibleParts v parts bc π = Finset.univ := by
  rw [boundaryIsWeakEnough] at hWeak
  rcases hWeak with ⟨π, hπ⟩
  refine ⟨π, hπ, ?_⟩
  ext j
  simp [feasibleParts, (Finset.mem_filter.mp hπ).2 j]

/-- Bennett Claim 1.4 application: the global witness furnished by a weak boundary cannot be a
splinter, because its feasible support is the full part set. -/
theorem weak_boundary_excludes_splintering
    {Φ : Type*} [DecidableEq Φ] [Fintype Φ]
    {m : ℕ} (v : Vocabulary Φ) (parts : Fin m → VTask v)
    (bc : BoundaryConditions v parts)
    (hWeak : boundaryIsWeakEnough v parts bc) :
    ∃ π ∈ restrictedCollective v parts bc,
      ¬ isSplinter v parts bc (feasibleParts v parts bc π) := by
  rcases weak_boundary_exhibits_global_policy v parts bc hWeak with ⟨π, hπ, hAll⟩
  refine ⟨π, hπ, ?_⟩
  intro hSplinter
  exact hSplinter.2.1.ne hAll

/-- Bennett §6 application: under over-constraint, every locally feasible policy is forced onto
a proper fragment of the parts. This is the application-level fragmentation consequence extracted
from Proposition 6.1, not a mere alias for the core splinter theorem. -/
theorem overconstrained_design_fragments_local_policy
    {Φ : Type*} [DecidableEq Φ] [Fintype Φ]
    {m : ℕ} (v : Vocabulary Φ) (parts : Fin m → VTask v)
    (bc : BoundaryConditions v parts)
    (hOver : isOverConstrained v parts bc)
    (π : Finset (Program Φ))
    (hFeasible : (feasibleParts v parts bc π).Nonempty) :
    feasibleParts v parts bc π ⊂ Finset.univ := by
  have hViable : ∃ j, (bc.restricted j).Nonempty := by
    rcases hFeasible with ⟨j, hj⟩
    exact ⟨j, ⟨π, (Finset.mem_filter.mp hj).2⟩⟩
  exact overconstraint_implies_splintering v parts bc hOver hViable π

end HeytingLean.StackTheory.Applications
