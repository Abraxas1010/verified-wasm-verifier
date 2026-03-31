import HeytingLean.Geo.GQRE.Core
import HeytingLean.Geo.GQRE.PMFlow

/-
Lightweight, compile-time checks for the GQRE / Perona–Malik flow.

These tests exercise the core operators on tiny fields and are
intended as smoke tests rather than full numerical proofs.
-/

namespace HeytingLean
namespace Tests
namespace Geo

open HeytingLean.Geo.GQRE

def constField (h w : Nat) (v : Float) : Field2 :=
  Array.replicate h (Array.replicate w v)

def unitSpike : Field2 :=
  #[
    #[0.0, 0.0],
    #[0.0, 1.0]
  ]

def demoParams : Params :=
  { alpha := 0.5 }

-- Evaluate the action on a constant 2×2 field; should be 0.
#eval Id.run (
  let φ : Field2 := constField 2 2 1.0
  let g := grad φ
  action demoParams g.gx g.gy
)

-- Evaluate the action on a simple 2×2 spike field; should be nonzero.
#eval Id.run (
  let g := grad unitSpike
  action demoParams g.gx g.gy
)

-- One Perona–Malik step on a constant field; used as a visual sanity check.
#eval Id.run (
  let φ : Field2 := constField 3 3 2.0
  pmStep demoParams 0.1 φ
)

end Geo
end Tests
end HeytingLean
