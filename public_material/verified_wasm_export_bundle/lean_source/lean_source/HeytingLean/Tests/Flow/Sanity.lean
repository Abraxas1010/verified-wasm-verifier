import HeytingLean.Metrics.Curvature
import HeytingLean.Bridges.Flow

open HeytingLean

namespace HeytingLean.Tests.Flow

def p0 : Metrics.FlowPoint := #[(0.0 : Float), 0.0]
def p1 : Metrics.FlowPoint := #[(1.0 : Float), 0.0]
def p2 : Metrics.FlowPoint := #[(1.0 : Float), 1.0]

def k01 : Float := Metrics.mengerCurvature p0 p1 p2 -- compile-only check

def tSmall : Bridges.FlowTraj := #[p0, p1, p2]
def tSmooth : Bridges.FlowTraj := Bridges.Flow.smoothOnce tSmall

def idNuc := Bridges.Flow.flowNucleusId

theorem idempotent_set_identity (S : Set Bridges.FlowTraj) : idNuc (idNuc S) = idNuc S := rfl

end HeytingLean.Tests.Flow

