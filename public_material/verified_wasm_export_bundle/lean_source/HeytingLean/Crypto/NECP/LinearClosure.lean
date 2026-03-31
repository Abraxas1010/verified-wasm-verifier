import HeytingLean.Crypto.NECP.SubspaceLattice

namespace HeytingLean
namespace Crypto
namespace NECP

open SubspaceLattice

section

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- Operator-driven closure by adjoining the visible range of the operator. -/
def linearClosure (T : M →ₗ[R] M) (U : Submodule R M) : Submodule R M :=
  U ⊔ LinearMap.range T

theorem linearClosure_extensive (T : M →ₗ[R] M) (U : Submodule R M) :
    U ≤ linearClosure T U :=
  le_sup_left

theorem linearClosure_monotone (T : M →ₗ[R] M) :
    Monotone (linearClosure T) := by
  intro U V hUV
  exact sup_le_sup hUV le_rfl

theorem linearClosure_idempotent (T : M →ₗ[R] M) (U : Submodule R M) :
    linearClosure T (linearClosure T U) = linearClosure T U := by
  simp [linearClosure]

theorem linearClosure_fixed_iff (T : M →ₗ[R] M) (U : Submodule R M) :
    linearClosure T U = U ↔ LinearMap.range T ≤ U := by
  constructor
  · intro h
    have : LinearMap.range T ≤ linearClosure T U := le_sup_right
    simpa [h] using this
  · intro h
    exact sup_eq_left.mpr h

end

@[simp] theorem linearClosure_projX_eq
    (U : Submodule SubspaceLattice.Bit SubspaceLattice.Plane) :
    linearClosure SubspaceLattice.projX U = U ⊔ SubspaceLattice.X := by
  simp [linearClosure, SubspaceLattice.projX_range_eq_X]

theorem linearClosure_meet_failure :
    linearClosure SubspaceLattice.projX (SubspaceLattice.Y ⊓ SubspaceLattice.D) ≠
      linearClosure SubspaceLattice.projX SubspaceLattice.Y ⊓
        linearClosure SubspaceLattice.projX SubspaceLattice.D := by
  rw [linearClosure_projX_eq, linearClosure_projX_eq, linearClosure_projX_eq]
  rw [SubspaceLattice.Y_inf_D_eq_bot, bot_sup_eq,
    sup_comm SubspaceLattice.Y SubspaceLattice.X,
    sup_comm SubspaceLattice.D SubspaceLattice.X,
    SubspaceLattice.X_sup_Y_eq_top, SubspaceLattice.X_sup_D_eq_top]
  simpa using SubspaceLattice.X_ne_top

end NECP
end Crypto
end HeytingLean
