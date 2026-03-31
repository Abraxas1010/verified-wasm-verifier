import HeytingLean.Varela.ECI
import HeytingLean.Varela.Waveforms
import HeytingLean.Varela.ReentryNucleus
import HeytingLean.Varela.MRBridge
import HeytingLean.Varela.TransportWitness
import HeytingLean.Varela.BridgeExemplar
import HeytingLean.Varela.Counterexamples
import HeytingLean.Varela.Fixtures
import HeytingLean.Varela.GenesisCompanion
import HeytingLean.Varela.OTMCompanion
import HeytingLean.Varela.ATPTargets

/-!
# HeytingLean.Varela

Concrete Varela/re-entry layer for HeytingLean.

This namespace is intentionally small and explicit:
- `ECI` and `Waveforms` give the finite carrier-level story,
- `ReentryNucleus` places that story inside an honest ambient nucleus,
- `MRBridge` shows how the same language lands in the existing `(M,R)` closure surface,
- `TransportWitness` packages the finite nucleus as a reusable transport oracle,
- `BridgeExemplar` mirrors one abstract transport pattern honestly on the finite carrier,
- `Counterexamples` records the exact over-strong claims the finite witness rejects,
- `Fixtures` centralizes deterministic finite behavior for later ATP/regression work,
- `GenesisCompanion` and `OTMCompanion` expose finite companions to specific abstract bridge families,
- `ATPTargets` exposes named prove/refute targets for the finite oracle.

The purpose is not to replace the abstract re-entry bridges elsewhere in the repo.
It is to provide a finite, executable companion that future transport work can use as
an honesty check and regression witness.
-/
