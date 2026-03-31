import HeytingLean.ClosingTheLoop.MR.ClosureOperator

/-!
# IteratedVirtual.Bridge.MRSystemConnection

Strict-only bridge from the existing Rosen-style `(M,R)` layer (`ClosingTheLoop.MR.*`) into the
IteratedVirtual narrative.

Key point (honest and provable):
- the loop-closing operator `closeSelector` is an **idempotent projection** on the selector space;
- its fixed points are the “organizationally closed” selectors (`IsClosed`).

We intentionally do **not** claim that `closeSelector` is a lattice nucleus here: a nucleus requires
an ambient meet-semilattice + inflationary law, and the MR selector space is not equipped with that
structure in the Tier‑1 MR scaffold.
-/

namespace HeytingLean
namespace IteratedVirtual
namespace Bridge

open HeytingLean.ClosingTheLoop

-- Universe parameters used for the projection carrier and the MR scaffold.
universe u v

/-- A minimal “projection” API: an endomap with idempotence. -/
structure IdemProjection (α : Sort u) where
  toFun : α → α
  idem : ∀ x, toFun (toFun x) = toFun x

instance {α : Sort u} : CoeFun (IdemProjection α) (fun _ => α → α) where
  coe p := p.toFun

namespace IdemProjection

@[simp] theorem idem_apply {α : Sort u} (p : IdemProjection α) (x : α) : p (p x) = p x :=
  p.idem x

end IdemProjection

/-!
## The MR loop-closing operator as a projection
-/

section
  variable {S : MR.MRSystem.{u, v}} {b : S.B} (RI : MR.RightInverseAt S b)

  /-- Package `closeSelector` as an idempotent projection. -/
  def closeSelectorProjection : IdemProjection (MR.Selector S) where
    toFun := MR.closeSelector S b RI
    idem := MR.closeSelector.idem (S := S) (b := b) (RI := RI)

  /-- “Organizational closure” as a fixed-point predicate: just `MR.IsClosed`. -/
  abbrev OrganizationallyClosed (RI : MR.RightInverseAt S b) (Φ : MR.Selector S) : Prop :=
    MR.IsClosed S b RI Φ

  /-- Fixed points of the projection are exactly the closed selectors. -/
  theorem organizationallyClosed_iff_fixed (Φ : MR.Selector S) :
      OrganizationallyClosed RI Φ ↔ closeSelectorProjection (RI := RI) Φ = Φ := by
    rfl

  /-- Closing any selector yields an organizationally closed one. -/
  theorem closeSelector_isClosed (Φ : MR.Selector S) :
      OrganizationallyClosed RI (MR.closeSelector S b RI Φ) := by
    exact MR.IsClosed.close_isClosed (S := S) (b := b) (RI := RI) Φ

end

end Bridge
end IteratedVirtual
end HeytingLean
