import HeytingLean.BountyHunter.AlgebraIR.Types
import HeytingLean.BountyHunter.AlgebraIR.Json
import HeytingLean.BountyHunter.AlgebraIR.Dominators
import HeytingLean.BountyHunter.AlgebraIR.CEI
import HeytingLean.BountyHunter.AlgebraIR.Examples
import HeytingLean.BountyHunter.AlgebraIR.Evidence
import HeytingLean.BountyHunter.AlgebraIR.EvidenceClosure
import HeytingLean.BountyHunter.AlgebraIR.Replay
import HeytingLean.BountyHunter.AlgebraIR.ToyEVMReplay

/-!
# HeytingLean.BountyHunter.AlgebraIR

Phase 0: AlgebraIR core + deterministic JSON + dominance-style checks.

This module is intentionally self-contained so it can be built and exercised
via a dedicated `lean_exe` without importing the rest of the (WIP) BountyHunter
stack.
-/
