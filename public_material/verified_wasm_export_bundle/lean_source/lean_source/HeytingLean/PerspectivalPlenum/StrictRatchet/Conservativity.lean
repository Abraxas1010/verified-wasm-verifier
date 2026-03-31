import HeytingLean.PerspectivalPlenum.StrictRatchet.Core
import HeytingLean.LoF.Bauer.DoubleNegation

namespace HeytingLean
namespace PerspectivalPlenum
namespace StrictRatchet

universe u v

/--
Generic conservativity contract for one translation lane.

`ProvableSrc` and `ProvableTgt` are intentionally abstract so each lane can
scope conservativity to the right fragment.
-/
structure ConservativeTranslation (Src : Type u) (Tgt : Type v) where
  translate : Src → Tgt
  ProvableSrc : Src → Prop
  ProvableTgt : Tgt → Prop
  sound : ∀ {φ : Src}, ProvableSrc φ → ProvableTgt (translate φ)
  conservative : ∀ {φ : Src}, ProvableTgt (translate φ) → ProvableSrc φ

namespace ConservativeTranslation

theorem iff_for_translated
    {Src : Type u} {Tgt : Type v}
    (T : ConservativeTranslation Src Tgt) (φ : Src) :
    T.ProvableSrc φ ↔ T.ProvableTgt (T.translate φ) := by
  exact ⟨T.sound, T.conservative⟩

namespace DoubleNegationLane

open HeytingLean.LoF

variable (α : Type u) [HeytingAlgebra α]

/-- Fragment object for the first conservativity lane: the regular (classical core) fragment. -/
abbrev Core : Type u := Bauer.ClassicalCore α

/-- Inclusion of the regular fragment into the ambient Heyting algebra. -/
def toHost : Core α → α := fun x => (x : α)

/-- Fragment-level provability model (`⊤ ≤ φ`). -/
def coreProvable (x : Core α) : Prop :=
  (⊤ : α) ≤ (x : α)

/-- Host provability after translation via double-negation closure. -/
def hostProvable (a : α) : Prop :=
  (⊤ : α) ≤ Bauer.doubleNegNucleus α a

private theorem core_fixed (x : Core α) :
    Bauer.doubleNegNucleus α (x : α) = (x : α) := by
  exact (Bauer.doubleNegNucleus_fixed_iff (α := α) (a := (x : α))).2 x.2

/-- First concrete lane: conservativity on the classical-core fragment. -/
def translation : ConservativeTranslation (Core α) α where
  translate := toHost α
  ProvableSrc := coreProvable α
  ProvableTgt := hostProvable α
  sound := by
    intro φ hφ
    simpa [toHost, coreProvable, hostProvable, core_fixed (α := α) φ] using hφ
  conservative := by
    intro φ hφ
    simpa [toHost, coreProvable, hostProvable, core_fixed (α := α) φ] using hφ

theorem conservativity_exact (φ : Core α) :
    (translation α).ProvableSrc φ
      ↔ (translation α).ProvableTgt ((translation α).translate φ) := by
  exact ConservativeTranslation.iff_for_translated (translation α) φ

/-- Unrestricted host provability can be pulled back only with an explicit fixed-point hypothesis. -/
def unrestrictedProvable (a : α) : Prop :=
  (⊤ : α) ≤ a

theorem unrestricted_of_hostProvable_of_fixed
    {a : α}
    (hProv : hostProvable α a)
    (hFix : Bauer.doubleNegNucleus α a = a) :
    unrestrictedProvable α a := by
  simpa [unrestrictedProvable, hostProvable, hFix] using hProv

end DoubleNegationLane
end ConservativeTranslation

end StrictRatchet
end PerspectivalPlenum
end HeytingLean
