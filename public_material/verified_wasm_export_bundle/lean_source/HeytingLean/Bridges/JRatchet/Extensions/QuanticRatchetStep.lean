import HeytingLean.Bridges.Nucleus.Extensions.QuanticNucleus
import HeytingLean.PerspectivalPlenum.ReReentryTower
import HeytingLean.CPP.MeetQuantale

/-!
# QuanticRatchetStep

This module adds a quantale-oriented ratchet-step interface inspired by
Sun (2019), emphasizing non-commutative behavior in quantic settings.
-/

namespace HeytingLean
namespace Bridges
namespace JRatchet
namespace Extensions
namespace QuanticRatchetStep

open HeytingLean.PerspectivalPlenum

universe u

/-- Alias for the quantic nucleus carrier used in this module. -/
abbrev QuanticNuc (Q : Type u) [Order.Frame Q] [Mul Q] :=
  HeytingLean.Bridges.Nucleus.Extensions.QuanticNucleus Q

/-- Pointwise order on quantic nuclei via their action map. -/
def leAct {Q : Type u} [Order.Frame Q] [Mul Q]
    (N₁ N₂ : QuanticNuc Q) : Prop :=
  ∀ a : Q, N₁.act a ≤ N₂.act a

/-- A ratchet step in the quantic-nucleus lane. -/
structure QuanticStep (Q : Type u) [Order.Frame Q] [Mul Q] where
  /-- Quantic-nucleus action. -/
  step : QuanticNuc Q → QuanticNuc Q
  /-- Extensiveness measured pointwise on `act`. -/
  extensive : ∀ N, leAct N (step N)
  /-- Monotonicity measured pointwise on `act`. -/
  monotoneAct : ∀ N₁ N₂, leAct N₁ N₂ → leAct (step N₁) (step N₂)
  /-- Idempotence on quantic nuclei. -/
  idempotent : ∀ N, step (step N) = step N

/-- Identity quantic ratchet step. -/
def idStep (Q : Type u) [Order.Frame Q] [Mul Q] : QuanticStep Q where
  step := fun N => N
  extensive := by
    intro N a
    exact le_rfl
  monotoneAct := by
    intro N₁ N₂ h
    exact h
  idempotent := by
    intro N
    rfl

/--
Convert a quantic ratchet step to a standard ratchet step via a bridge
(`lift`/`forget`) and explicit compatibility obligations.
-/
def toRatchetStep
    {Q : Type u} [Order.Frame Q] [Mul Q]
    (S : QuanticStep Q)
    (lift : Nucleus Q → QuanticNuc Q)
    (forget : QuanticNuc Q → Nucleus Q)
    (_forgetLift : ∀ J : Nucleus Q, forget (lift J) = J)
    (stepExtensive : ∀ J : Nucleus Q, J ≤ forget (S.step (lift J)))
    (stepMonotone :
      ∀ {J K : Nucleus Q}, J ≤ K →
        forget (S.step (lift J)) ≤ forget (S.step (lift K)))
    (stepIdempotent :
      ∀ J : Nucleus Q,
        forget (S.step (lift (forget (S.step (lift J))))) =
          forget (S.step (lift J))) :
    RatchetStep Q where
  step := fun J => forget (S.step (lift J))
  extensive := stepExtensive
  monotone := by
    intro J K hJK
    exact stepMonotone hJK
  idempotent := stepIdempotent

/-- Composition of quantic ratchet steps need not commute in general (Sun 2019). -/
def quanticRatchetNoncommutative : Prop :=
  ∃ (Q : Type) (_ : Order.Frame Q) (_ : Mul Q)
    (S T : QuanticStep Q) (N : QuanticNuc Q),
    S.step (T.step N) ≠ T.step (S.step N)

/-- Lightweight witness package for a noncommutative quantic lane. -/
structure NoncommutativeWitness where
  Q : Type u
  instFrame : Order.Frame Q
  instMul : Mul Q
  S : QuanticStep Q
  T : QuanticStep Q
  N : QuanticNuc Q
  hne : S.step (T.step N) ≠ T.step (S.step N)

end QuanticRatchetStep
end Extensions
end JRatchet
end Bridges
end HeytingLean
