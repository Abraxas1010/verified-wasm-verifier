import HeytingLean.Genesis.EigenformSoup.Runner
import HeytingLean.LoF.Nucleus
import HeytingLean.LoF.Instances

/-!
# Genesis.EigenformSoup.Bridge

WS4 bridge layer:
- transports WS1-WS3 nucleus-fixed claims to LoF `Reentry` fixedness,
- keeps bridge assumptions explicit,
- avoids claiming direct `Reentry` semantics without witness data.
-/

namespace HeytingLean.Genesis.EigenformSoup

open HeytingLean
open HeytingLean.LoF

/-- Reentry object over the soup support carrier. -/
abbrev SupportReentry : Type := LoF.Reentry Support

/-- Explicit bridge witness from a soup nucleus to a LoF reentry nucleus. -/
structure ReentryBridgeWitness (nuc : SoupNucleus) where
  reentry : SupportReentry
  agrees : ∀ S : Support, nuc S = reentry.nucleus S

/-- WS4 readiness: explicit bridge witness plus bridge law gate. -/
def BridgeReady (nuc : SoupNucleus) : Prop :=
  ∃ _ : ReentryBridgeWitness nuc, ReentryBridgeLaw nuc

/-- Any soup eigenform is fixed by the bridged reentry nucleus. -/
theorem eigenform_to_reentry_fixed
    {nuc : SoupNucleus}
    (bridge : ReentryBridgeWitness nuc)
    {S : Support}
    (hEigen : isEigenform nuc S) :
    bridge.reentry.nucleus S = S := by
  have hNuc : nuc S = S := hEigen
  calc
    bridge.reentry.nucleus S = nuc S := (bridge.agrees S).symm
    _ = S := hNuc

/-- Stabilization-event supports are fixed by the bridged reentry nucleus. -/
theorem stabilizationEvent_to_reentry_fixed
    {nuc : SoupNucleus}
    (bridge : ReentryBridgeWitness nuc)
    (e : StabilizationEvent nuc) :
    bridge.reentry.nucleus e.support = e.support :=
  eigenform_to_reentry_fixed bridge e.fixed

/-- End-of-run stabilized supports are fixed by the bridged reentry nucleus. -/
theorem runSoup_to_reentry_fixed
    {nuc : SoupNucleus}
    (bridge : ReentryBridgeWitness nuc)
    (cfg : SoupConfig)
    (S : Support)
    (hS : S ∈ (runSoup nuc cfg).stabilized) :
    bridge.reentry.nucleus S = S := by
  exact eigenform_to_reentry_fixed bridge (runSoup_sound nuc cfg S hS)

/-- The default collapse policy is not bridge-ready for direct reentry claims. -/
theorem collapsePolicy_not_bridgeReady :
    ¬ BridgeReady collapsePolicy := by
  intro h
  rcases h with ⟨_bridge, hLaw⟩
  exact collapsePolicy_not_reentryBridgeLaw hLaw

end HeytingLean.Genesis.EigenformSoup
