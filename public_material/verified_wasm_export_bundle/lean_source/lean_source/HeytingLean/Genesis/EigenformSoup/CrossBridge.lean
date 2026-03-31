import HeytingLean.Genesis.EigenformSoup.Bridge
import HeytingLean.Genesis.EigenformSoup.Observer
import HeytingLean.Genesis.EigenformSoup.PhaseGates

/-!
# Genesis.EigenformSoup.CrossBridge

Cross-module bridge theorems connecting runner, observer, extraction, and WS9 gates.
-/

namespace HeytingLean.Genesis.EigenformSoup

theorem extractionGates_hold (nuc : SoupNucleus) (cfg : SoupConfig) :
    extractionCompileGate nuc cfg ∧ extractionSemanticParityGate nuc cfg := by
  refine ⟨?_, ?_⟩
  · exact extractionCompileGate_holds nuc cfg
  · exact extractionSemanticParityGate_holds nuc cfg

theorem runSoupAux_to_reentry_fixed
    {nuc : SoupNucleus}
    (bridge : ReentryBridgeWitness nuc)
    (fuel : Nat)
    (s : SoupState nuc)
    (hPrev : ∀ S, S ∈ s.stabilized → isEigenform nuc S)
    (S : Support)
    (hS : S ∈ (runSoupAux fuel s).stabilized) :
    bridge.reentry.nucleus S = S := by
  have hEigen : isEigenform nuc S :=
    runSoupAux_preserves_eigenforms (nuc := nuc) fuel s hPrev S hS
  exact eigenform_to_reentry_fixed bridge hEigen

theorem certifyRun_to_reentry_fixed
    {nuc : SoupNucleus}
    (bridge : ReentryBridgeWitness nuc)
    (cfg : SoupConfig)
    (S : Support)
    (hS : S ∈ (certifyRun nuc cfg).finalState.stabilized) :
    bridge.reentry.nucleus S = S := by
  have hEigen : isEigenform nuc S := (certifyRun nuc cfg).allEigenforms S hS
  exact eigenform_to_reentry_fixed bridge hEigen

theorem observeTrace_runSoupTrace_length_eq_snapshots
    (nuc : SoupNucleus)
    (observer : SoupObserver)
    (cfg : SoupConfig) :
    (observeTrace nuc observer (runSoupTrace nuc cfg)).length =
      (runSoupTraceSnapshots nuc cfg).length := by
  calc
    (observeTrace nuc observer (runSoupTrace nuc cfg)).length = (runSoupTrace nuc cfg).length := by
      exact observeTrace_length observer (runSoupTrace nuc cfg)
    _ = cfg.fuel + 1 := runSoupTrace_length nuc cfg
    _ = (runSoupTraceSnapshots nuc cfg).length := by
      symm
      exact runSoupTraceSnapshots_length nuc cfg

end HeytingLean.Genesis.EigenformSoup
