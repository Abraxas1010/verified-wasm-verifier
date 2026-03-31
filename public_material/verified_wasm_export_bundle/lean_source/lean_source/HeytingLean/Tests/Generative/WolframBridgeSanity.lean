import HeytingLean.Generative.WolframBridge

namespace HeytingLean.Tests.Generative

open HeytingLean.Generative.WolframBridge
open HeytingLean.HossenfelderNoGo.HeytingBoundary
open HeytingLean.NucleusGrafting

example {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : BoundaryNucleus L) :
    isBoolean N ↔ NucleusInvariant N :=
  hossenfelder_isBoolean_iff_nucleusInvariant N

example {n : Nat} (z : Int) :
    ¬ NucleusInvariant (graftBoundaryNucleus (n := n) z) :=
  graft_not_nucleusInvariant (n := n) z

example {n : Nat} (z : Int) :
    boundaryGap (graftBoundaryNucleus (n := n) z)
      (∅ : Set (ActivationVector n)) ≠ ∅ :=
  boundaryGap_bot_nonempty (n := n) z

end HeytingLean.Tests.Generative
