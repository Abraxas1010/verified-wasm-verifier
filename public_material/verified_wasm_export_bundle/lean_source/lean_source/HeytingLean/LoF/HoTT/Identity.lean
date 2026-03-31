/-!
HoTT-style identity layer for LoF.

We currently use Lean's built-in equality but expose a dedicated
identity alias and notations so that later phases can migrate to a
non-`Prop` path type if desired. This keeps the current development
kernel-safe and proof-compatible while already presenting a
HoTT-flavoured API (`Id`, `FormId`) that can later be upgraded to a
genuine path type.
-/

namespace HeytingLean
namespace LoF

universe u

namespace HoTT

/-- HoTT-inspired identity alias for LoF.

For now, `Id x y` is simply definitionally equal to `x = y`.  This
means we inherit all of Lean's equality infrastructure while keeping
the freedom to later replace `Id` with a genuine path type in a
controlled HoTT namespace. -/
abbrev Id {α : Type u} (x y : α) : Prop := x = y

notation:50 x " ⟡ " y => Id x y

/-! ### Specialization: identity for LoF propositions/forms -/

section FormId

/-- Internal identity for LoF "forms" or propositions. Currently this is
just equality (via `Id`), but it has its own notation so we can migrate
later without touching clients. -/
abbrev FormId {Form : Type u} (P Q : Form) : Prop := Id P Q

notation:50 P " ≃ₚ " Q => FormId P Q

end FormId

/-! ### Basic groupoid-style operations on `Id`

Even though `Id` is currently just propositional equality, we expose a
small HoTT-flavoured API (refl, symm, trans, recursor) so that other
modules and the blueprint can treat it as an identity type.  These are
thin wrappers around Lean's built-in equality principles. -/

/-- Reflexivity of the identity relation. -/
theorem Id.refl {α : Type u} (x : α) : Id x x := rfl

/-- Symmetry of the identity relation. -/
theorem Id.symm {α : Type u} {x y : α} : Id x y → Id y x := by
  intro h
  exact Eq.symm h

/-- Transitivity of the identity relation. -/
theorem Id.trans {α : Type u} {x y z : α} :
    Id x y → Id y z → Id x z := by
  intro h₁ h₂
  exact Eq.trans h₁ h₂

/-- Recursor / J-rule for `Id`, phrased as a wrapper around
`Eq.rec`.  This is sufficient for basic path-induction style
reasoning in the current `Prop`-level setting. -/
def Id.rec {α : Type u} {x : α}
    {P : α → Prop} (h : P x) :
    ∀ {y}, Id x y → P y
  | _, rfl => h

end HoTT

/-!
We re-export the main aliases at the `HeytingLean.LoF` level so that
existing code can continue to write `Id` and `FormId` without
changing imports, while the fully-qualified names live in
`HeytingLean.LoF.HoTT`.
-/

export HoTT (Id FormId)

end LoF
end HeytingLean
