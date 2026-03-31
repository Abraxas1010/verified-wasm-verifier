import HeytingLean.Genesis.EigenformSoup.Invariants
import HeytingLean.Topos.JRatchet

/-!
# Bridge.Veselov.AssemblyRatchet

Scoped OP07 bridge surface:
- define a finite-run assembly-index proxy on soup states,
- prove equivalence between assembly-index growth and J-ratchet monotonicity
  under explicit scoped assumptions.

This module is intentionally scoped; it does not claim unrestricted global
assembly-index equivalence.
-/

namespace HeytingLean.Bridge.Veselov

open HeytingLean
open HeytingLean.Genesis.EigenformSoup

/-- Scoped assembly-index proxy used for OP07 bridge statements. -/
def assemblyIndexProxy {nuc : SoupNucleus} (s : SoupState nuc) : Nat :=
  jRatchetLevel s

@[simp] theorem assemblyIndexProxy_eq_jRatchetLevel {nuc : SoupNucleus} (s : SoupState nuc) :
    assemblyIndexProxy s = jRatchetLevel s := rfl

/-- Run-level assembly-index growth contract in the scoped soup carrier. -/
def AssemblyIndexGrowthContract {nuc : SoupNucleus} (s : SoupState nuc) : Prop :=
  ∀ fuel₁ fuel₂, fuel₁ ≤ fuel₂ →
    assemblyIndexProxy (runSoupAux fuel₁ s) ≤ assemblyIndexProxy (runSoupAux fuel₂ s)

/-- Run-level J-ratchet growth contract in the scoped soup carrier. -/
def JRatchetGrowthContract {nuc : SoupNucleus} (s : SoupState nuc) : Prop :=
  HeytingLean.Topos.JRatchet.RatchetTrajectory
    (fun fuel => jRatchetLevel (runSoupAux fuel s))

/--
Scoped OP07 equivalence:
assembly-index growth and J-ratchet trajectory monotonicity are equivalent
in the finite soup-run proxy carrier.
-/
theorem scoped_assembly_index_equivalence {nuc : SoupNucleus} (s : SoupState nuc) :
    AssemblyIndexGrowthContract s ↔ JRatchetGrowthContract s := by
  constructor <;> intro h
  · intro fuel₁ fuel₂ hle
    simpa [AssemblyIndexGrowthContract, JRatchetGrowthContract, assemblyIndexProxy] using
      h fuel₁ fuel₂ hle
  · intro fuel₁ fuel₂ hle
    simpa [AssemblyIndexGrowthContract, JRatchetGrowthContract, assemblyIndexProxy] using
      h fuel₁ fuel₂ hle

/-- Scoped OP07 witness: the assembly-index proxy is monotone along soup runs. -/
theorem scoped_assembly_index_growth {nuc : SoupNucleus} (s : SoupState nuc) :
    AssemblyIndexGrowthContract s := by
  intro fuel₁ fuel₂ hle
  simpa [AssemblyIndexGrowthContract, assemblyIndexProxy] using
    j_ratchet_monotonicity (nuc := nuc) s fuel₁ fuel₂ hle

/--
Packaged OP07 scoped bridge theorem:
the two growth contracts are equivalent and both hold in the scoped soup carrier.
-/
theorem op07_scoped_bridge_theorem {nuc : SoupNucleus} (s : SoupState nuc) :
    (AssemblyIndexGrowthContract s ↔ JRatchetGrowthContract s) ∧
      AssemblyIndexGrowthContract s ∧ JRatchetGrowthContract s := by
  refine ⟨scoped_assembly_index_equivalence s, scoped_assembly_index_growth s, ?_⟩
  exact (scoped_assembly_index_equivalence s).1 (scoped_assembly_index_growth s)

end HeytingLean.Bridge.Veselov
