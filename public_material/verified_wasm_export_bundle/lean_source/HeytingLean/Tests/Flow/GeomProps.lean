import HeytingLean.Metrics.Curvature

open HeytingLean.Metrics

namespace HeytingLean.Tests.Flow

def sq0 : FlowPoint := #[(0.0 : Float), 0.0]
def sq1 : FlowPoint := #[(1.0 : Float), 0.0]
def sq2 : FlowPoint := #[(1.0 : Float), 1.0]
def sq3 : FlowPoint := #[(0.0 : Float), 1.0]

def square : Array FlowPoint := #[sq0, sq1, sq2, sq3, sq0]

def perSq : Float := perimeter2D square
def areaSq : Float := area2D square

-- compile-only sanity: values are computed; no assertions needed under strict build

end HeytingLean.Tests.Flow

