import HeytingLean.Genesis.EigenformSoup.Invariants

/-!
# Genesis.EigenformSoup.Convergence

Run-level convergence facts for deterministic EigenformSoup execution.
-/

namespace HeytingLean.Genesis.EigenformSoup

theorem carrierSize_runSoupAux_eq {nuc : SoupNucleus} (fuel : Nat) (s : SoupState nuc) :
    carrierSize (runSoupAux fuel s) = carrierSize s := by
  induction fuel generalizing s with
  | zero =>
      simp [runSoupAux]
  | succ fuel ih =>
      simp only [runSoupAux]
      calc
        carrierSize (runSoupAux fuel (stepSoup s)) = carrierSize (stepSoup s) := ih (s := stepSoup s)
        _ = carrierSize s := carrierSize_step_eq (nuc := nuc) s

theorem entropy_nonincrease_runSoupAux {nuc : SoupNucleus} (fuel : Nat) (s : SoupState nuc) :
    entropyMetric (runSoupAux fuel s) ≤ entropyMetric s := by
  induction fuel generalizing s with
  | zero =>
      simp [runSoupAux]
  | succ fuel ih =>
      have hStep : entropyMetric (stepSoup s) ≤ entropyMetric s :=
        entropy_nonincrease_step (nuc := nuc) s
      have hTail : entropyMetric (runSoupAux fuel (stepSoup s)) ≤ entropyMetric (stepSoup s) :=
        ih (s := stepSoup s)
      simpa [runSoupAux] using Nat.le_trans hTail hStep

theorem ratchetClick_strict_jRatchet_runSoupAux
    {nuc : SoupNucleus} (fuel : Nat) (s : SoupState nuc) (hClick : ratchetClick s) :
    jRatchetLevel s < jRatchetLevel (runSoupAux (fuel + 1) s) := by
  have hStep : jRatchetLevel s < jRatchetLevel (stepSoup s) := by
    simpa [ratchetClick] using hClick
  have hTail : jRatchetLevel (stepSoup s) ≤ jRatchetLevel (runSoupAux fuel (stepSoup s)) :=
    jRatchetLevel_runSoupAux_monotone (nuc := nuc) fuel (stepSoup s)
  have hLift : jRatchetLevel s < jRatchetLevel (runSoupAux fuel (stepSoup s)) :=
    lt_of_lt_of_le hStep hTail
  simpa [runSoupAux] using hLift

theorem three_conservation_laws_runSoupAux {nuc : SoupNucleus} (fuel : Nat) (s : SoupState nuc) :
    carrierSize (runSoupAux fuel s) = carrierSize s ∧
      jRatchetLevel s ≤ jRatchetLevel (runSoupAux fuel s) ∧
      entropyMetric (runSoupAux fuel s) ≤ entropyMetric s := by
  refine ⟨carrierSize_runSoupAux_eq (nuc := nuc) fuel s, ?_, ?_⟩
  · exact jRatchetLevel_runSoupAux_monotone (nuc := nuc) fuel s
  · exact entropy_nonincrease_runSoupAux (nuc := nuc) fuel s

end HeytingLean.Genesis.EigenformSoup
