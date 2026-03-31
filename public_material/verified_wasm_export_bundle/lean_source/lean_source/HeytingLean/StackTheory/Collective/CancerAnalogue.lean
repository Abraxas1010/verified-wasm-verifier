import HeytingLean.StackTheory.Collective.BoundaryConditions

namespace HeytingLean.StackTheory

variable {Φ : Type*} [DecidableEq Φ] [Fintype Φ]

/-- Bennett §6, Proposition 6.1: if every part accepted `π`, then `π` would lie in the
restricted collective set. Under over-constraint this is impossible, so the feasible parts form
a proper subset. -/
theorem overconstraint_implies_splintering
    {m : ℕ} (v : Vocabulary Φ) (parts : Fin m → VTask v)
    (bc : BoundaryConditions v parts)
    (hOver : isOverConstrained v parts bc)
    (hViable : ∃ j, (bc.restricted j).Nonempty)
    (π : Finset (Program Φ)) :
    feasibleParts v parts bc π ⊂ Finset.univ := by
  constructor
  · exact Finset.filter_subset _ _
  · intro hAll
    have hMem : π ∈ restrictedCollective v parts bc := by
      refine Finset.mem_filter.mpr ?_
      constructor
      · rcases hViable with ⟨j, _⟩
        have hj : j ∈ feasibleParts v parts bc π := hAll (Finset.mem_univ j)
        exact (mem_correctPolicies.mp ((bc.sub j) ((Finset.mem_filter.mp hj).2))).1
      · intro k
        exact (Finset.mem_filter.mp (hAll (Finset.mem_univ k))).2
    rw [hOver] at hMem
    exact Finset.notMem_empty _ hMem

/-- Bennett §6: any locally feasible continuation under over-constraint lives on a splinter. -/
theorem overconstraint_yields_splinter
    {m : ℕ} (v : Vocabulary Φ) (parts : Fin m → VTask v)
    (bc : BoundaryConditions v parts)
    (hOver : isOverConstrained v parts bc)
    (π : Finset (Program Φ))
    (hFeasible : (feasibleParts v parts bc π).Nonempty) :
    isSplinter v parts bc (feasibleParts v parts bc π) := by
  have hViable : ∃ j, (bc.restricted j).Nonempty := by
    rcases hFeasible with ⟨j, hj⟩
    refine ⟨j, ⟨π, (Finset.mem_filter.mp hj).2⟩⟩
  have hProper :
      feasibleParts v parts bc π ⊂ Finset.univ :=
    overconstraint_implies_splintering v parts bc hOver hViable π
  refine ⟨hFeasible, hProper, ?_⟩
  refine ⟨π, Finset.mem_filter.mpr ?_⟩
  constructor
  · rcases hFeasible with ⟨j, hj⟩
    exact (mem_correctPolicies.mp ((bc.sub j) ((Finset.mem_filter.mp hj).2))).1
  · intro j hj
    exact (Finset.mem_filter.mp hj).2

end HeytingLean.StackTheory
