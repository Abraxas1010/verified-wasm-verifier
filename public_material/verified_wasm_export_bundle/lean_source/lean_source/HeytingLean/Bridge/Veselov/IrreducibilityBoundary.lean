import HeytingLean.Bridge.Veselov.TimeReduction

/-!
# Bridge.Veselov.IrreducibilityBoundary

Scoped OP01 bridge surface:
explicit boundary criterion and obstruction theorem for finite-potential
reduction systems.
-/

namespace HeytingLean.Bridge.Veselov

universe u

/-- Boundary criterion: the reduction potential is already at terminal zero. -/
def IrreducibilityBoundary (S : Type u) (R : DiscreteReduction S) (s : S) : Prop :=
  R.potential s = 0

/-- Strict one-step reduction witness outside the boundary. -/
def StrictReductionAvailable (S : Type u) (R : DiscreteReduction S) (s : S) : Prop :=
  R.potential (R.step s) < R.potential s

/-- Boundary states are fixed by the reduction step. -/
theorem boundary_fixed
    (S : Type u) (R : DiscreteReduction S) (s : S)
    (h : IrreducibilityBoundary S R s) :
    R.step s = s := by
  exact terminal_state (S := S) R h

/-- Boundary states cannot have strict one-step descent. -/
theorem boundary_obstruction
    (S : Type u) (R : DiscreteReduction S) (s : S)
    (h : IrreducibilityBoundary S R s) :
    ¬ StrictReductionAvailable S R s := by
  intro hdesc
  have hstep : R.step s = s := boundary_fixed S R s h
  have hdesc' : R.potential (R.step s) < R.potential s := by
    simpa [StrictReductionAvailable] using hdesc
  rw [hstep] at hdesc'
  exact Nat.lt_irrefl _ hdesc'

/-- Every state is either at the boundary or admits one-step strict descent. -/
theorem irreducibility_boundary_obstruction
    (S : Type u) (R : DiscreteReduction S) (s : S) :
    IrreducibilityBoundary S R s ∨ StrictReductionAvailable S R s := by
  rcases one_step_description (S := S) R s with h0 | h1
  · exact Or.inl h0.1
  · exact Or.inr h1.2

/--
Packaged OP01 scoped theorem:
- boundary criterion is fixed-point stable,
- and every state satisfies boundary-or-descent dichotomy.
-/
theorem op01_scoped_boundary_theorem
    (S : Type u) (R : DiscreteReduction S) (s : S) :
    (IrreducibilityBoundary S R s → R.step s = s) ∧
      (IrreducibilityBoundary S R s ∨ StrictReductionAvailable S R s) := by
  exact ⟨boundary_fixed S R s, irreducibility_boundary_obstruction S R s⟩

end HeytingLean.Bridge.Veselov
