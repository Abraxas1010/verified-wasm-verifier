import HeytingLean.Integration.MagmaAsymptotic.NucleusPreserved
import HeytingLean.AsymptoticSafety.ScaleSymmetry
import HeytingLean.AsymptoticSafety.NucleusInstance
import HeytingLean.Magma.Separation.MagmaticClass
import HeytingLean.Magma.Bridge.ScaleInvariance
import HeytingLean.Magma.Bridge.NucleusProjection

namespace HeytingLean.Integration.MagmaAsymptotic

open HeytingLean.AsymptoticSafety
open HeytingLean.Magma
open HeytingLean.Magma.Separation
open HeytingLean.Magma.Bridge

/-- A property of coupling regions is AS-scale-invariant when the UV nucleus
preserves it. -/
def ASScaleInvariant (sys : BetaSystem) (φ : CouplingRegion → Prop) : Prop :=
  NucleusPreserved (coreNucleus sys) φ

theorem asScaleInvariant_iff (sys : BetaSystem) (φ : CouplingRegion → Prop) :
    ASScaleInvariant sys φ ↔ ∀ U, φ U → φ (rgRestrict sys U) := by
  rfl

variable {A : Type*} [HeytingLean.Magma.MagmaticAtoms A] [HeytingLean.Magma.MagmaticUniverse A]
  [HeytingLean.Magma.PairEncoding A] [HeytingLean.Magma.ProductEncoding A]

/-- A scale-invariant pointwise predicate propagates across a nucleus-fixed
family. This is the honest Magma-side bridge available from the current
`MagmaticNucleus` API: `omega_R` only certifies fixed families, not arbitrary-set
preservation. -/
theorem magmatic_fixed_family_preserves_scaleInvariant
    (N : MagmaticNucleus A) (φ : Magma A → Prop) (hSI : ScaleInvariant φ)
    {x : Magma A} (hx : x ∈ omega_R N) (hxφ : φ x) :
    ∀ ⦃y : Magma A⦄, y ∈ N.nucleus.R (familyOf x) → φ y := by
  intro y hy
  have hfix : N.nucleus.R (familyOf x) = familyOf x := by
    simpa [omega_R] using hx
  have hy_family : y ∈ familyOf x := by
    rw [hfix] at hy
    exact hy
  have hy_le : y ≤ x := by
    simpa [familyOf] using hy_family
  exact hSI hxφ hy_le

theorem scale_invariance_structural_correspondence
    (sys : BetaSystem) :
    (∀ φ : CouplingRegion → Prop,
      ASScaleInvariant sys φ ↔ NucleusPreserved (coreNucleus sys) φ) ∧
    (∀ U V : CouplingRegion,
      orderNucleus sys U = U → orderNucleus sys V = V →
      orderNucleus sys (U ⊓ V) = U ⊓ V) := by
  constructor
  · intro φ
    rfl
  · intro U V hU hV
    calc
      orderNucleus sys (U ⊓ V) = orderNucleus sys U ⊓ orderNucleus sys V :=
        (orderNucleus sys).map_inf' U V
      _ = U ⊓ V := by rw [hU, hV]

end HeytingLean.Integration.MagmaAsymptotic
