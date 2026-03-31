import Mathlib.Order.GaloisConnection.Basic

/-!
# Comparison nucleus specification
-/

namespace HeytingLean
namespace LoF
namespace Comparison

open scoped Classical

universe u v

/-- Core data for the comparison nucleus: a Galois connection `f ⊣ g`. -/
structure CompSpec (L : Type u) (Ω : Type v)
    [CompleteLattice L] [CompleteLattice Ω] where
  f : L → Ω
  g : Ω → L
  mon_f : Monotone f
  mon_g : Monotone g
  gc : GaloisConnection f g

/-- Strong hypothesis pack: `f` preserves binary meets. -/
structure StrongHyp (L : Type u) (Ω : Type v)
    [CompleteLattice L] [CompleteLattice Ω]
    extends CompSpec L Ω where
  map_inf : ∀ x y : L, f (x ⊓ y) = f x ⊓ f y

namespace StrongHyp

variable {L : Type u} {Ω : Type v}
variable [CompleteLattice L] [CompleteLattice Ω]

/-- Coercion to the underlying comparison spec. -/
instance : Coe (StrongHyp L Ω) (CompSpec L Ω) := ⟨StrongHyp.toCompSpec⟩

@[simp] lemma unit (S : StrongHyp L Ω) (x : L) :
    x ≤ S.g (S.f x) :=
  (S.gc x (S.f x)).mp le_rfl

@[simp] lemma counit (S : StrongHyp L Ω) (u : Ω) :
    S.f (S.g u) ≤ u :=
  (S.gc (S.g u) u).mpr le_rfl

@[simp] lemma monotone_f (S : StrongHyp L Ω) : Monotone S.f := S.mon_f
@[simp] lemma monotone_g (S : StrongHyp L Ω) : Monotone S.g := S.mon_g

end StrongHyp

/-- Frobenius-style hypothesis pack: a weaker sufficient set of laws. -/
structure FrobeniusHyp (L : Type u) (Ω : Type v)
    [CompleteLattice L] [CompleteLattice Ω] extends CompSpec L Ω where
  frobenius : ∀ x : L, ∀ u : Ω, f (x ⊓ g u) = f x ⊓ u
  meet_lb : ∀ x y : L, f x ⊓ f y ≤ f (x ⊓ y)

namespace FrobeniusHyp

variable {L : Type u} {Ω : Type v}
variable [CompleteLattice L] [CompleteLattice Ω]

instance : Coe (FrobeniusHyp L Ω) (CompSpec L Ω) :=
  ⟨FrobeniusHyp.toCompSpec⟩

@[simp] lemma unit (S : FrobeniusHyp L Ω) (x : L) :
    x ≤ S.g (S.f x) :=
  (S.gc x (S.f x)).mp le_rfl

@[simp] lemma counit (S : FrobeniusHyp L Ω) (u : Ω) :
    S.f (S.g u) ≤ u :=
  (S.gc (S.g u) u).mpr le_rfl

@[simp] lemma monotone_f (S : FrobeniusHyp L Ω) : Monotone S.f := S.mon_f
@[simp] lemma monotone_g (S : FrobeniusHyp L Ω) : Monotone S.g := S.mon_g

end FrobeniusHyp

end Comparison
end LoF
end HeytingLean
