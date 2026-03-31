import Mathlib.Data.Set.Lattice
import Mathlib.Order.Nucleus
import Mathlib.Order.Sublocale
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Tactic

/-!
# Spectral Heyting scaffolding (Phase 5)

This module provides an **order-theoretic** “spectral Heyting” layer intended to support the
Fourier/spectral parts of the "Quantum on a Laptop" plan **without** importing heavy analysis.

Design choices (honest + laptop-scale):

* We model “spectral opens” for a discrete spectrum `ι` as `Set ι`. This is a complete Boolean
  algebra, hence an `Order.Frame`, hence a (complete) Heyting algebra.
* We implement a small family of nuclei on these opens. The basic one is the “band/core closure”
  `U ↦ U ∪ Ω`, whose fixed points are exactly the opens containing `Ω`.
* Any analytic claim (e.g. that some Fourier functor preserves Heyting implication) is recorded as
  an explicit interface/assumption, **not** as a global postulate.
-/

namespace HeytingLean
namespace Analysis

universe u v

/-! ## Spectral opens -/

/-- “Spectral opens” for a spectrum index type `ι` (discrete model). -/
abbrev SpectralOpens (ι : Type u) : Type u := Set ι

namespace SpectralOpens

variable {ι : Type u}

@[simp] lemma mem_mk (U : SpectralOpens ι) (i : ι) : i ∈ U ↔ i ∈ (U : Set ι) := Iff.rfl

end SpectralOpens

/-! ## A nucleus on spectral opens: add a fixed spectral core -/

namespace SpectralNucleus

variable {ι : Type u}

/-- The “core closure” nucleus: `U ↦ U ∪ Ω`. Fixed points are opens containing `Ω`. -/
def coreClosure (Ω : SpectralOpens ι) : Nucleus (SpectralOpens ι) where
  toFun U := U ∪ Ω
  map_inf' U V := by
    ext x
    constructor
    · intro hx
      rcases hx with hxUV | hxΩ
      · exact And.intro (Or.inl hxUV.1) (Or.inl hxUV.2)
      · exact And.intro (Or.inr hxΩ) (Or.inr hxΩ)
    · intro hx
      rcases hx with ⟨hU, hV⟩
      rcases hU with hU | hΩ
      · rcases hV with hV | hΩ'
        · exact Or.inl ⟨hU, hV⟩
        · exact Or.inr hΩ'
      · exact Or.inr hΩ
  idempotent' U := by
    intro x hx
    rcases hx with hxUΩ | hxΩ
    · rcases hxUΩ with hxU | hxΩ'
      · exact Or.inl hxU
      · exact Or.inr hxΩ'
    · exact Or.inr hxΩ
  le_apply' U := by
    intro x hx
    exact Or.inl hx

@[simp] lemma coreClosure_apply (Ω U : SpectralOpens ι) :
    coreClosure (ι := ι) Ω U = U ∪ Ω := rfl

lemma coreClosure_fixed_iff (Ω U : SpectralOpens ι) :
    coreClosure (ι := ι) Ω U = U ↔ Ω ⊆ U := by
  constructor
  · intro h x hx
    have : x ∈ coreClosure (ι := ι) Ω U := by
      -- `x ∈ Ω` implies `x ∈ U ∪ Ω`.
      simpa [coreClosure] using Or.inr hx
    simpa [h] using this
  · intro hΩ
    ext x
    constructor
    · intro hx
      rcases hx with hxU | hxΩ
      · exact hxU
      · exact hΩ hxΩ
    · intro hxU
      exact Or.inl hxU

/-- The “spectral Heyting core” as a sublocale: the fixed points of `coreClosure Ω`. -/
abbrev Core (Ω : SpectralOpens ι) : Type u :=
  (coreClosure (ι := ι) Ω).toSublocale

@[simp] lemma mem_Core_iff_contains (Ω U : SpectralOpens ι) :
    U ∈ (coreClosure (ι := ι) Ω).toSublocale ↔ Ω ⊆ U := by
  constructor
  · intro hU
    rcases (coreClosure (ι := ι) Ω).mem_toSublocale.1 hU with ⟨V, hV⟩
    -- `U = V ∪ Ω`, hence `Ω ⊆ U`.
    intro x hx
    have hxVΩ : x ∈ coreClosure (ι := ι) Ω V := by
      simpa [coreClosure] using (Or.inr hx : x ∈ V ∪ Ω)
    simpa [hV] using hxVΩ
  · intro hΩ
    -- If `Ω ⊆ U`, then `U` is a fixed point, hence in the image.
    have hfix : coreClosure (ι := ι) Ω U = U :=
      (coreClosure_fixed_iff (ι := ι) Ω U).2 hΩ
    exact (coreClosure (ι := ι) Ω).mem_toSublocale.2 ⟨U, hfix⟩

end SpectralNucleus

/-! ## Fourier/Heyting interface (statement-only) -/

namespace FourierHeyting

/-- A **statement-only** record: a candidate Fourier map on opens, together with the (future) claim
that it preserves Heyting implication.

We keep this as an interface/hypothesis: proving it requires analytic content which is out of scope
for Phase 5. -/
structure PreservesHeyting (X : Type u) (Y : Type v) [Order.Frame X] [Order.Frame Y] where
  /-- The underlying map (intended “Fourier on opens”). -/
  F : FrameHom X Y
  /-- The key deferred property: preservation of Heyting implication. -/
  map_himp : ∀ a b : X, F (a ⇨ b) = (F a) ⇨ (F b)

namespace PreservesHeyting

variable {X : Type u} {Y : Type v} [Order.Frame X] [Order.Frame Y]

@[simp] lemma map_inf (H : PreservesHeyting X Y) (a b : X) :
    H.F (a ⊓ b) = H.F a ⊓ H.F b := by
  exact H.F.map_inf' a b

@[simp] lemma map_top (H : PreservesHeyting X Y) : H.F ⊤ = (⊤ : Y) := by
  exact H.F.map_top'

end PreservesHeyting

end FourierHeyting

end Analysis
end HeytingLean
