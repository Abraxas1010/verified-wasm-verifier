import Mathlib.Order.Nucleus
import Mathlib.Order.Sublocale
import Mathlib.Order.Heyting.Basic
import HeytingLean.Quantum.Translate.Modality
import HeytingLean.Quantum.Translate.Core
import HeytingLean.Quantum.OML.Sasaki

open scoped Classical

namespace HeytingLean.Quantum.Translate

variable {α : Type _} [Order.Frame α]

/-- Fixed points of a modality's nucleus, viewed as a sublocale. -/
abbrev Omega (M : Modality α) : Type _ := M.J.toSublocale

namespace Omega

variable (M : Modality α)

/-- Build an element of `Omega M` from an ambient point together with a fixed-point proof. -/
@[simp] def mk (a : α) (h : M.J a = a) : Omega M := ⟨a, ⟨a, h⟩⟩

@[simp] lemma closed (x : Omega M) : M.J (x : α) = x := by
  rcases x.property with ⟨b, hb⟩
  calc
    M.J (x : α) = M.J (M.J b) := by simp [hb]
    _ = M.J b := by simp
    _ = (x : α) := by simp [hb]

/-- Infimum in `Ω_M`. -/
def inf (x y : Omega M) : Omega M := x ⊓ y

/-- Supremum in `Ω_M`. -/
def sup (x y : Omega M) : Omega M := x ⊔ y

/-- Top element in `Ω_M`. -/
def top : Omega M := ⊤

/-- Bottom element in `Ω_M`. -/
def bot : Omega M := ⊥

section Heyting

variable [HeytingAlgebra α]

/-- Heyting implication in `Ω_M`, inherited from the ambient Heyting algebra. -/
def imp (x y : Omega M) : Omega M := x ⇨ y

end Heyting

/-- In the Heyting core `Ω_{T.M}`, the translated Sasaki hook lies below the Heyting implication.
    This wraps the ambient bridge lemma into the closed-world algebra. -/
lemma sasakiHook_le_himp
    {β : Type _} {α : Type _}
    [HeytingLean.Quantum.OML.OrthocomplementedLattice β]
    [HeytingLean.Quantum.OML.OrthomodularLattice β]
    [Order.Frame α] [HasCompl α]
    (T : QLMap β α) [QLMap.ComplPreserving T] (a b : β) :
    Omega.mk (M := T.M) (T.M.J (T.tr (HeytingLean.Quantum.OML.sasakiHook a b)))
        (by simp)
      ≤
      Omega.mk (M := T.M) (T.M.J ((T.tr a)ᶜ ⊔ T.tr b))
        (by simp) := by
  -- ambient bridge
  have h :=
    QLMap.sasakiHook_le_translated_nucleus_imp
      (F := T) (hCompl := inferInstance) (a := a) (b := b)
  -- close left side
  have h' := T.M.J.monotone h
  simpa [T.M.idempotent] using h'

end Omega

end HeytingLean.Quantum.Translate
