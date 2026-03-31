import HeytingLean.Bridges.Nucleus.Extensions.Prenucleus
import HeytingLean.Logic.ReflectionProgression

namespace HeytingLean
namespace Bridges
namespace Nucleus
namespace Extensions

open HeytingLean.Logic

namespace Prenucleus

variable {α : Type*} [Order.Frame α]

/-- Stabilize a prenucleus by taking the least nucleus dominating its action. -/
noncomputable def stabilize (P : Prenucleus α) : _root_.Nucleus α :=
  nucleusClosure (α := α) P.act

/-- The prenucleus action is below its stabilized nucleus. -/
theorem le_stabilize_apply (P : Prenucleus α) (a : α) :
    P.act a ≤ stabilize (α := α) P a := by
  simpa [stabilize] using
    (le_nucleusClosure (α := α) P.act a)

/-- Characteristic minimality of stabilization. -/
theorem stabilize_le_of_dominates (P : Prenucleus α)
    {n : _root_.Nucleus α}
    (hn : n ∈ dominating (α := α) P.act) :
    stabilize (α := α) P ≤ n := by
  simpa [stabilize] using
    (nucleusClosure_le_of_mem (α := α) (f := P.act) (n := n) hn)

/-- Stabilization is extensive as a nucleus. -/
theorem le_stabilize (P : Prenucleus α) (a : α) : a ≤ stabilize (α := α) P a :=
  _root_.Nucleus.le_apply (n := stabilize (α := α) P) (x := a)

/-- Stabilization preserves finite meets as a nucleus. -/
theorem stabilize_map_inf (P : Prenucleus α) (a b : α) :
    stabilize (α := α) P (a ⊓ b) = stabilize (α := α) P a ⊓ stabilize (α := α) P b :=
  _root_.Nucleus.map_inf (n := stabilize (α := α) P) (x := a) (y := b)

/-- If a prenucleus is already idempotent, the associated nucleus dominates stabilization. -/
theorem stabilize_le_idempotent_hull (P : Prenucleus α)
    (hidem : ∀ a, P.act (P.act a) = P.act a) :
    stabilize (α := α) P ≤
      ({ toFun := P.act
         map_inf' := P.map_inf
         idempotent' := by intro a; exact le_of_eq (hidem a)
         le_apply' := P.extensive } : _root_.Nucleus α) := by
  -- This is direct from leastness of `stabilize`.
  exact stabilize_le_of_dominates (α := α) P (n :=
      { toFun := P.act
        map_inf' := P.map_inf
        idempotent' := by intro a; exact le_of_eq (hidem a)
        le_apply' := P.extensive })
      (by intro x; exact le_rfl)

end Prenucleus

end Extensions
end Nucleus
end Bridges
end HeytingLean
