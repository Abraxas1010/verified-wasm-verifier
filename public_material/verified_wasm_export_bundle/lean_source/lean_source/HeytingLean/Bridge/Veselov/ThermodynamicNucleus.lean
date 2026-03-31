import HeytingLean.Genesis.EigenformSoup.Invariants

/-!
# Bridge.Veselov.ThermodynamicNucleus

Scoped OP03 bridge surface:
connect dissipative (entropy non-increase) contracts with nucleus-compatible
ratchet monotonicity on soup trajectories.
-/

namespace HeytingLean.Bridge.Veselov

open HeytingLean.Genesis.EigenformSoup

/-- One-step dissipative contract: entropy surrogate does not increase. -/
def DissipativeEntropyContract {nuc : SoupNucleus} (s : SoupState nuc) : Prop :=
  entropyMetric (stepSoup s) ≤ entropyMetric s

/-- One-step thermodynamic+nucleus compatibility contract. -/
def ThermodynamicNucleusContract {nuc : SoupNucleus} (s : SoupState nuc) : Prop :=
  jRatchetLevel s ≤ jRatchetLevel (stepSoup s) ∧
    entropyMetric (stepSoup s) ≤ entropyMetric s

/-- Dissipative contract holds on the scoped soup carrier. -/
theorem dissipativeEntropyContract_holds
    {nuc : SoupNucleus} (s : SoupState nuc) :
    DissipativeEntropyContract s := by
  simpa [DissipativeEntropyContract] using entropy_nonincrease_step (nuc := nuc) s

/-- Thermodynamic+nucleus one-step contract holds on the scoped soup carrier. -/
theorem thermodynamicNucleusContract_holds
    {nuc : SoupNucleus} (s : SoupState nuc) :
    ThermodynamicNucleusContract s := by
  exact ⟨jRatchetLevel_step_monotone (nuc := nuc) s,
    entropy_nonincrease_step (nuc := nuc) s⟩

/-- Run-level ratchet monotonicity bridge from dissipative trajectory semantics. -/
theorem thermodynamic_run_contract
    {nuc : SoupNucleus} (s : SoupState nuc)
    (fuel₁ fuel₂ : Nat) (hle : fuel₁ ≤ fuel₂) :
    jRatchetLevel (runSoupAux fuel₁ s) ≤ jRatchetLevel (runSoupAux fuel₂ s) := by
  exact j_ratchet_monotonicity (nuc := nuc) s fuel₁ fuel₂ hle

/--
Packaged OP03 scoped theorem:
- one-step thermodynamic+nucleus contract is satisfied,
- dissipative entropy contract is satisfied,
- and run-level ratchet monotonicity remains available.
-/
theorem op03_scoped_bridge_theorem
    {nuc : SoupNucleus} (s : SoupState nuc) :
    ThermodynamicNucleusContract s ∧
      DissipativeEntropyContract s ∧
      (∀ fuel₁ fuel₂, fuel₁ ≤ fuel₂ →
        jRatchetLevel (runSoupAux fuel₁ s) ≤ jRatchetLevel (runSoupAux fuel₂ s)) := by
  refine ⟨thermodynamicNucleusContract_holds (s := s),
    dissipativeEntropyContract_holds (s := s), ?_⟩
  intro fuel₁ fuel₂ hle
  exact thermodynamic_run_contract (s := s) fuel₁ fuel₂ hle

end HeytingLean.Bridge.Veselov
