import HeytingLean.Core.Nucleus
import Mathlib.Order.Heyting.Basic

/-!
# Fixed-Point Heyting Algebra (bundle core)

Given a Heyting algebra `L` and an R-nucleus `N`, the fixed points of `N` form
a substructure. For the standalone bundle we only expose the carrier and a few
basic operations; the full Heyting-algebra instance can be added later.

We also record the nucleus-induced implication:

`a →ₙ b := N.R (a ⇨ b)`.
-/

namespace HeytingLean
namespace Core

open scoped Classical

namespace Nucleus

variable {L : Type*} [HeytingAlgebra L]

/-- Nucleus-induced Heyting implication: `a →ₙ b = R (a ⇨ b)`. -/
def himp (N : Nucleus L) (a b : L) : L :=
  N.R (a ⇨ b)

end Nucleus

/-- Fixed points of a nucleus, packaged as a structure for bundling.

The `property` field uses equality rather than a set membership predicate,
so it composes well with `simp`.
-/
structure FixedPointAlgebra (L : Type*) [HeytingAlgebra L] (N : Nucleus L) where
  /-- Underlying element. -/
  val : L
  /-- Fixed-point condition. -/
  property : N.R val = val

namespace FixedPointAlgebra

variable {L : Type*} [HeytingAlgebra L] {N : Nucleus L}

instance : CoeOut (FixedPointAlgebra L N) L :=
  ⟨FixedPointAlgebra.val⟩

@[simp] theorem coe_mk (x : L) (hx : N.R x = x) :
    ((FixedPointAlgebra.mk (L := L) (N := N) x hx : FixedPointAlgebra L N) : L) = x :=
  rfl

/-- Meet of fixed points is a fixed point. -/
def inf (a b : FixedPointAlgebra L N) : FixedPointAlgebra L N where
  val := a.val ⊓ b.val
  property := N.fixed_eq_closed_inf a.property b.property

/-- `R ⊤` is a fixed point. -/
def top : FixedPointAlgebra L N where
  val := N.R ⊤
  property := N.idempotent ⊤

/-- `R ⊥` is a fixed point. -/
def bot : FixedPointAlgebra L N where
  val := N.R ⊥
  property := N.idempotent ⊥

end FixedPointAlgebra

end Core
end HeytingLean
