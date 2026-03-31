import Mathlib.Order.BooleanAlgebra.Set
import HeytingLean.Crypto.NECP.LinearClosure
import HeytingLean.Crypto.NECP.PrincipalNucleus

namespace HeytingLean
namespace Crypto
namespace NECP

section

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- Observation family consisting of subspaces containing the visible operator range. -/
def invariantFamily (T : M →ₗ[R] M) : Set (Submodule R M) :=
  {U | LinearMap.range T ≤ U}

@[simp] theorem mem_invariantFamily {T : M →ₗ[R] M} {U : Submodule R M} :
    U ∈ invariantFamily T ↔ LinearMap.range T ≤ U :=
  Iff.rfl

/-- Genuine nucleus on the frame of observable subspace-families. -/
def linearInvariantObservationNucleus (T : M →ₗ[R] M) :
    Nucleus (Set (Submodule R M)) :=
  principalNucleus (invariantFamily T)

theorem linearClosure_mem_invariantFamily (T : M →ₗ[R] M) (U : Submodule R M) :
    linearClosure T U ∈ invariantFamily T := by
  show LinearMap.range T ≤ U ⊔ LinearMap.range T
  exact le_sup_right

theorem linearClosure_enters_observation
    (T : M →ₗ[R] M) (S : Set (Submodule R M)) {U : Submodule R M}
    (hU : U ∈ S) :
    linearClosure T U ∈ linearInvariantObservationNucleus T (linearClosure T '' S) := by
  exact Or.inr ⟨U, hU, rfl⟩

theorem linearNucleusBridge_exists (T : M →ₗ[R] M) :
    ∃ n : Nucleus (Set (Submodule R M)),
      ∀ (S : Set (Submodule R M)) {U : Submodule R M},
        U ∈ S → linearClosure T U ∈ n (linearClosure T '' S) := by
  refine ⟨linearInvariantObservationNucleus T, ?_⟩
  intro S U hU
  exact linearClosure_enters_observation T S hU

end

end NECP
end Crypto
end HeytingLean
