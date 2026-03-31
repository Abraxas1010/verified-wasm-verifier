import HeytingLean.MirandaDynamics.Reach
import HeytingLean.MirandaDynamics.TKFT.Reaching
import HeytingLean.MirandaDynamics.TKFT.Category
import HeytingLean.MirandaDynamics.FixedPoint.PeriodicNucleus
import HeytingLean.MirandaDynamics.Billiards.CantorEncoding
import HeytingLean.MirandaDynamics.Billiards.CantorNucleus
import HeytingLean.MirandaDynamics.Computation.TuringMachine
import HeytingLean.MirandaDynamics.Topology.BettiComplexity
import HeytingLean.MirandaDynamics.Undecidability.Transfers
import HeytingLean.MirandaDynamics.External.Interfaces
import HeytingLean.MirandaDynamics.Discrete.HaltingToPeriodic
import HeytingLean.MirandaDynamics.Fluids.ContactGeometry
import HeytingLean.MirandaDynamics.Fluids.CosymplecticGeometry
import HeytingLean.MirandaDynamics.Fluids.EtnyreGhrist
import HeytingLean.MirandaDynamics.Fluids.HarmonicNS
import HeytingLean.MirandaDynamics.Fluids.TuringComplete

/-!
# MirandaDynamics (umbrella)

This umbrella module collects the Lean-realistic spine of the “Miranda integration” project:

- reachability/simulation tooling (re-exported),
- TKFT-style reaching relations and their compositional laws,
- a nucleus/fixed-point view of “periodicity” (specialized to the existing Flow lens),
- undecidability-transfer lemmas (halting → dynamical predicate).

The analytic geometry/PDE results from the external literature are *referenced in docs* but are not
reproved here.
-/
