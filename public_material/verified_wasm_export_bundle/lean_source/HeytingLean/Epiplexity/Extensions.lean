import HeytingLean.Epiplexity.Crypto.Witnesses
import HeytingLean.Epiplexity.Bridges.CausalEmergence
import HeytingLean.Epiplexity.Bridges.LoF
import HeytingLean.Epiplexity.Quantum.LoFCircuitEpiplexity
import HeytingLean.Epiplexity.Applications.Curriculum

/-!
# Epiplexity extensions (umbrella)

This module is an import-only aggregator for optional extensions that connect Epiplexity to
other parts of HeytingLean (bridges, applications, etc.).

The core Epiplexity development lives in `HeytingLean.Epiplexity.*`; keeping extensions behind
this file makes it easier to keep the core stable while iterating on research-driven additions.
-/
