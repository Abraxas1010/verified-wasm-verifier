import Mathlib.Algebra.Order.Quantale
import Mathlib.Order.Nucleus
import HeytingLean.CPP.MeetQuantale

namespace HeytingLean
namespace Bridges
namespace Nucleus
namespace Extensions

universe u

/-- Quantic prenucleus: prenucleus laws plus multiplicative preservation. -/
structure QuanticPrenucleus (Q : Type u) [CompleteLattice Q] [Mul Q] where
  act : Q → Q
  extensive : ∀ a, a ≤ act a
  map_inf : ∀ a b, act (a ⊓ b) = act a ⊓ act b
  map_mul : ∀ a b, act (a * b) = act a * act b

namespace QuanticPrenucleus

variable {Q : Type u} [CompleteLattice Q] [Mul Q]

/-- Monotonicity inherited from extensiveness + inf-preservation. -/
theorem monotone (P : QuanticPrenucleus Q) : Monotone P.act := by
  intro a b hab
  have hInf : a ⊓ b = a := inf_eq_left.mpr hab
  calc
    P.act a = P.act (a ⊓ b) := by simp [hInf]
    _ = P.act a ⊓ P.act b := P.map_inf a b
    _ ≤ P.act b := inf_le_right

end QuanticPrenucleus

/-- Quantic nucleus: a quantic prenucleus with idempotence. -/
structure QuanticNucleus (Q : Type u) [CompleteLattice Q] [Mul Q]
    extends QuanticPrenucleus Q where
  idempotent : ∀ a, act (act a) = act a

namespace QuanticNucleus

variable {Q : Type u} [CompleteLattice Q] [Mul Q]

/-- Fixed points are multiplicatively closed under a quantic nucleus. -/
theorem fixed_mul (N : QuanticNucleus Q) {a b : Q}
    (ha : N.act a = a) (hb : N.act b = b) :
    N.act (a * b) = a * b := by
  simpa [ha, hb] using N.map_mul a b

/-- Identity quantic nucleus (canonical baseline). -/
def idQuanticNucleus (Q : Type u) [CompleteLattice Q] [Mul Q] : QuanticNucleus Q where
  act := id
  extensive := by intro a; exact le_rfl
  map_inf := by intro a b; rfl
  map_mul := by intro a b; rfl
  idempotent := by intro a; rfl

/-- Forgetful map into Mathlib nuclei. -/
def toMathlibNucleus (N : QuanticNucleus Q) : _root_.Nucleus Q where
  toFun := N.act
  map_inf' := N.map_inf
  idempotent' := fun a => le_of_eq (N.idempotent a)
  le_apply' := N.extensive

@[simp] theorem toMathlibNucleus_apply (N : QuanticNucleus Q) (a : Q) :
    toMathlibNucleus N a = N.act a := rfl

/-- Worked quantale example on the meet-quantale wrapper. -/
def meetQuantaleIdExample (α : Type u) [Order.Frame α] :
    QuanticNucleus (HeytingLean.CPP.MeetQuantale α) :=
  idQuanticNucleus (Q := HeytingLean.CPP.MeetQuantale α)

end QuanticNucleus

end Extensions
end Nucleus
end Bridges
end HeytingLean
