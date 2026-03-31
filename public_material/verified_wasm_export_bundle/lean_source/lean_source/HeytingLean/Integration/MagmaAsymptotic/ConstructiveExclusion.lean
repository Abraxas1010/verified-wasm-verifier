import HeytingLean.Integration.MagmaAsymptotic.NucleusPartition
import HeytingLean.Integration.MagmaAsymptotic.ScaleInvarianceUnification
import HeytingLean.AsymptoticSafety.Predictions.DarkMatter
import HeytingLean.AsymptoticSafety.NucleusInstance

namespace HeytingLean.Integration.MagmaAsymptotic

open HeytingLean.AsymptoticSafety

/-- The AS analogue of a magmatic downward-closed property: preservation under
the UV nucleus on coupling regions. -/
abbrev ASMagmatic (sys : BetaSystem) (φ : CouplingRegion → Prop) : Prop :=
  ASScaleInvariant sys φ

theorem positive_portal_not_asMagmatic (sys : BetaSystem)
    (hscreen : PortalScreeningHypothesis sys) :
    ¬ ASMagmatic sys (fun U => ∃ g ∈ carrier U, 0 < g.portalCoupling) := by
  intro hMag
  have hPortalPositive : ∃ g ∈ carrier portalPositiveRegion, 0 < g.portalCoupling := by
    refine ⟨portalTestPoint, portalTestPoint_mem_portalPositiveRegion, ?_⟩
    simp [portalTestPoint]
  have hRestricted := hMag portalPositiveRegion hPortalPositive
  rcases hRestricted with ⟨g, hg, hpos⟩
  have hzero : g.portalCoupling = 0 :=
    portal_zero_of_uvSafe_and_screening sys g hscreen hg.2
  simp [hzero] at hpos

theorem portal_excluded_on_uvSafe (sys : BetaSystem)
    (hscreen : PortalScreeningHypothesis sys) :
    ∀ g : CouplingPoint, isUVSafe sys g → g.portalCoupling = 0 :=
  fun g hsafe => portal_zero_of_uvSafe_and_screening sys g hscreen hsafe

theorem exclusion_is_non_magmatic_consequence (sys : BetaSystem)
    (hscreen : PortalScreeningHypothesis sys) :
    ¬ ASMagmatic sys (fun U => ∃ g ∈ carrier U, 0 < g.portalCoupling) ∧
    uvSafeSet sys ⊆ carrier (portalExclusionRegion sys) := by
  exact ⟨positive_portal_not_asMagmatic sys hscreen, no_simplest_WIMP sys hscreen⟩

end HeytingLean.Integration.MagmaAsymptotic
