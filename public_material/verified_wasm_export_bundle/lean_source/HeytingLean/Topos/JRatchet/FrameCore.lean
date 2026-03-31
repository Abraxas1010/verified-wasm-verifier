import Mathlib.Order.Sublocale

/-!
# JRatchet: nucleus fixed-point core on frames (mathlib wrapper)

This module is a thin, paper-friendly wrapper around mathlib’s locale/nucleus theory:

* a nucleus `n : Nucleus X` on a frame `X` determines a sublocale `n.toSublocale`,
* the elements of `n.toSublocale` are (definitionally) the `n`-closed truth values, and
* joins/sups inside the fixed-point core are computed by **closing** ambient joins/sups.

We prove a small set of explicit “closure formulas” that are convenient for downstream
ontology/blueprint writing, without re-deriving any of the underlying theory.
-/

namespace HeytingLean
namespace Topos
namespace JRatchet

open Order

universe u

variable {X : Type u} [Order.Frame X]

variable (n : Nucleus X)

@[simp]
lemma coe_restrict_toSublocale (x : X) :
    ((n.toSublocale.restrict x : n.toSublocale) : X) = n x := by
  have hx :
      n.toSublocale.restrict x = (⟨n x, x, rfl⟩ : n.toSublocale) :=
    Nucleus.restrict_toSublocale (n := n) x
  exact congrArg Subtype.val hx

/-! ## Joins and suprema are “closed joins/sups” -/

theorem sup_eq_restrict (a b : n.toSublocale) :
    a ⊔ b = n.toSublocale.restrict ((a : X) ⊔ (b : X)) :=
  (n.toSublocale.giRestrict.l_sup_u (a := a) (b := b)).symm

theorem coe_sup (a b : n.toSublocale) :
    ((a ⊔ b : n.toSublocale) : X) = n ((a : X) ⊔ (b : X)) := by
  have h :
      (a ⊔ b : n.toSublocale) = n.toSublocale.restrict ((a : X) ⊔ (b : X)) :=
    sup_eq_restrict (n := n) a b
  have h' :
      ((a ⊔ b : n.toSublocale) : X)
        = ((n.toSublocale.restrict ((a : X) ⊔ (b : X)) : n.toSublocale) : X) :=
    congrArg Subtype.val h
  exact h'.trans (coe_restrict_toSublocale (n := n) ((a : X) ⊔ (b : X)))

theorem iSup_eq_restrict {ι : Sort _} (f : ι → n.toSublocale) :
    (⨆ i, f i) = n.toSublocale.restrict (⨆ i, (f i : X)) :=
  (n.toSublocale.giRestrict.l_iSup_u (f := f)).symm

theorem coe_iSup {ι : Sort _} (f : ι → n.toSublocale) :
    ((⨆ i, f i : n.toSublocale) : X) = n (⨆ i, (f i : X)) := by
  have h :
      (⨆ i, f i : n.toSublocale) = n.toSublocale.restrict (⨆ i, (f i : X)) :=
    iSup_eq_restrict (n := n) f
  have h' :
      ((⨆ i, f i : n.toSublocale) : X)
        = ((n.toSublocale.restrict (⨆ i, (f i : X)) : n.toSublocale) : X) :=
    congrArg Subtype.val h
  exact h'.trans (coe_restrict_toSublocale (n := n) (⨆ i, (f i : X)))

end JRatchet
end Topos
end HeytingLean

