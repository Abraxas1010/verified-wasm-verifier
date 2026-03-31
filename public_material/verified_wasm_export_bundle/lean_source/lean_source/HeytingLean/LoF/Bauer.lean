import HeytingLean.LoF.Bauer.DoubleNegation
import HeytingLean.LoF.Bauer.Domains
import HeytingLean.LoF.Bauer.DomainTheory
import HeytingLean.LoF.Bauer.Eigenforms
import HeytingLean.LoF.Bauer.LawvereFixedPoint
import HeytingLean.LoF.Bauer.LawvereCategorical
import HeytingLean.LoF.Bauer.GeometricMorphisms
import HeytingLean.LoF.Bauer.Nuclei
import HeytingLean.LoF.Bauer.SyntheticComputability
import HeytingLean.LoF.Bauer.ToposBridge

/-!
# Bauer integration (LoF-facing)

Lean-facing hooks for ideas from Andrej Bauer’s synthetic/topos-theoretic viewpoint:

* `HeytingLean.LoF.Bauer.doubleNegNucleus` — the double-negation (Booleanization) nucleus;
* `HeytingLean.LoF.Bauer.ClassicalCore` — the Boolean algebra of regular elements;
* `HeytingLean.LoF.Bauer.range_subset_range_iff` — order/range inclusion facts for nuclei.
* `HeytingLean.LoF.Bauer.FrameGeomEmbedding` — a frame-level geometric-embedding interface for lens transports;
* `HeytingLean.LoF.Comparison.comparisonGeomEmbedding` — comparison `enc/dec` packaged as such (under meet/top hypotheses).
* `HeytingLean.LoF.Bauer.SyntheticComputability.World` — a nucleus-based synthetic computability “world” interface;
* `HeytingLean.LoF.Bauer.SyntheticComputability.Toy.world` — a tiny `Set Bool` demo instance for QA.
* `HeytingLean.LoF.Bauer.DomainTheory` — ωCPPO scaffolding and a Kleene least fixed point theorem;
* `HeytingLean.LoF.Bauer.CountablyBasedDomain` — a lightweight interface for domains with a countable basis;
* `HeytingLean.LoF.Bauer.localOperatorOfPropNucleus` — build a `Topos.LocalOperator (Type u)` from a `Nucleus Prop`.
-/
