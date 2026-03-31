import HeytingLean.Security.Model.Unified

namespace HeytingLean.Tests.Security.ModelSanity

open scoped BigOperators

open HeytingLean.Security.Model

/-!
# Security model sanity checks

These are small compile-time checks that:
- exercise the definitions introduced in Phase 1; and
- avoid adding new global lemmas (use `example` blocks instead).
-/

section Computational

open Filter

example : Computational.Negligible (fun _n : ℕ => (0 : ℝ)) := by
  dsimp [Computational.Negligible]
  exact
    (Asymptotics.superpolynomialDecay_zero (l := Filter.atTop) (k := fun n : ℕ => (n : ℝ)))

end Computational

section InformationTheoretic

open HeytingLean.Probability.InfoTheory

example {α : Type} [Fintype α] (P : FinDist α) :
    InformationTheoretic.statisticalDistance P P = 0 := by
  classical
  simp [InformationTheoretic.statisticalDistance]

example {M C : Type} [Fintype C] (μ : FinDist C) :
    InformationTheoretic.perfectSecrecy (fun (_m : M) => μ) := by
  intro m₀ m₁ c
  rfl

end InformationTheoretic

section Physical

open HeytingLean.Constructor.CT

example {σ : Type} (T : HeytingLean.Constructor.CT.Task σ) :
    ¬ Physical.CTSecure (J := HeytingLean.Constructor.CT.Examples.trivial σ) T := by
  intro hSecure
  exact hSecure (HeytingLean.Constructor.CT.Examples.trivial_possible (σ := σ) T)

end Physical

end HeytingLean.Tests.Security.ModelSanity
