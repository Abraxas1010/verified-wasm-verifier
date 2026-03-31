import HeytingLean.FractalUniverse.NucleusConnection.ReEntryGrowth
import HeytingLean.FractalUniverse.Core.DynamicGraph
import HeytingLean.Varela.ReentryNucleus
import HeytingLean.Core.Nucleus

/-!
# ReEntry Irreversibility Collection

GENUINE BRIDGE: imports from FractalUniverse (ReEntryGrowth, DynamicGraph)
AND Varela (ReentryNucleus) and re-exports both irreversibility results.

Both subsystems produce `Core.Nucleus` instances (FractalUniverse via
`NucleusConnection.toNucleus`, Varela via `stageNucleus` which is a
Mathlib `Nucleus`). Both prove a negation result about self-referential
closure:
- Graph growth: no injection V(t+1) ↪ V(t) (cardinality irreversibility)
- Varela: ¬(autonomous ⊔ autonomousᶜ = ⊤) (non-classicality)

The common ingredient is the nucleus axioms: an idempotent closure that
introduces genuine novelty produces non-invertibility. The bridge collects
these results and makes the shared pattern explicit.

## Scope note

The formal unification (a single abstract theorem implying both) would
require showing cardinality irreversibility and lattice non-classicality
are instances of the same abstract negation — a follow-on conjecture.
This module honestly collects and re-exports the proved results.
-/

namespace HeytingLean.FractalUniverse.Bridges

open NucleusConnection

/-- DynamicGraph growth has the re-entry containment property — direct
    reuse of FractalUniverse infrastructure. -/
def graphReEntry (G : Core.DynamicGraph) : ReEntryGrowth G :=
  mkReEntryGrowth G

/-- Graph growth is irreversible: no injection from V(t+1) into V(t)
    exists (strict cardinality increase). Direct reuse. -/
theorem graph_growth_irreversible (G : Core.DynamicGraph) (t : ℕ)
    [Fintype (G.V t)] [Fintype (G.V (t + 1))] :
    ¬ ∃ (_ : G.V (t + 1) ↪ G.V t), True :=
  growth_irreversible G t

/-- Graph growth is causally irreversible: no edge-preserving embedding
    from V(t+1) back into V(t). Direct reuse. -/
theorem graph_no_causal_retraction (G : Core.DynamicGraph) (t : ℕ)
    [Fintype (G.V t)] [Fintype (G.V (t + 1))] :
    ¬ ∃ (π : G.V (t + 1) ↪ G.V t),
      ∀ u v, G.E (t + 1) u v → G.E t (π u) (π v) :=
  growth_no_causal_retraction G t

/-- Varela's non-classicality: the autonomous state's complement in the
    nucleus fixed-point sublattice fails excluded middle. Direct reuse. -/
theorem varela_autonomous_not_classical :
    ¬ (Varela.ReentryStage.eciToOmega .autonomous ⊔
       (Varela.ReentryStage.eciToOmega .autonomous)ᶜ =
       (⊤ : Varela.ReentryStage.StageOmega)) :=
  Varela.omega_autonomous_not_classical

/-- The FractalUniverse nucleus: mkReEntryGrowth produces a ReEntryGrowth
    from any DynamicGraph. Re-exported for the bridge pattern. -/
theorem fractalUniverse_reentry_containment (G : Core.DynamicGraph) (t : ℕ) :
    ∃ (ι : G.V t ↪ G.V (t + 1)),
      ∀ u v, G.E t u v → G.E (t + 1) (ι u) (ι v) :=
  dynamic_graph_has_reentry G t

end HeytingLean.FractalUniverse.Bridges
