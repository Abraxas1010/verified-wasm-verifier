import HeytingLean.Core.Nucleus

/-!
# IteratedVirtual.Bridge.MRClosure

Strict-only: a tiny “(M,R)-style closure” record whose `β` operator becomes a
`HeytingLean.Core.Nucleus` when given the standard closure axioms.

This is intentionally **not** a full Rosen (M,R) development. HeytingLean already contains a
Tier-1 (M,R) scaffold under `HeytingLean.ClosingTheLoop.MR.*`. Here we only provide a minimal,
portable bridge piece that can be used both in IteratedVirtual discussions and in other layers.
-/

namespace HeytingLean
namespace IteratedVirtual
namespace Bridge

open HeytingLean.Core

/-!
## Minimal closure operator (“β”)

We isolate only the idempotence law here; extensivity and meet-preservation are supplied when
building a `Nucleus`.
-/

structure ClosureSystem (X : Type*) where
  /-- The closure/replication operator `β`. -/
  β : X → X
  /-- Idempotence: `β (β x) = β x`. -/
  idem : ∀ x, β (β x) = β x

namespace ClosureSystem

variable {X : Type*}

/-- If a closure system is extensive and meet-preserving, it gives a nucleus. -/
def toNucleus [SemilatticeInf X] [OrderBot X] (sys : ClosureSystem X)
    (extensive : ∀ x, x ≤ sys.β x)
    (meet_preserving : ∀ x y, sys.β (x ⊓ y) = sys.β x ⊓ sys.β y) :
    Nucleus X where
  R := sys.β
  extensive := extensive
  idempotent := sys.idem
  meet_preserving := meet_preserving

/-- “Organizational closure”: fixed points of `β`. -/
def IsClosed (sys : ClosureSystem X) (x : X) : Prop :=
  sys.β x = x

theorem IsClosed_iff (sys : ClosureSystem X) (x : X) :
    sys.IsClosed x ↔ sys.β x = x :=
  Iff.rfl

end ClosureSystem

end Bridge
end IteratedVirtual
end HeytingLean
