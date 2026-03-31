import HeytingLean.IteratedVirtual.VirtualComposition

/-!
# IteratedVirtual.Spiral

Geometric “DNA-like spiral” embedding as a **computable** helix.

This does not attempt to prove any energy-minimization theorem; it provides:
- a `Point3` record,
- a helix parameterization,
- an embedding that maps “step index” ↦ point on a helix.
-/

namespace HeytingLean
namespace IteratedVirtual

open CategoryTheory

structure Point3 where
  x : Float
  y : Float
  z : Float
deriving Repr

namespace Point3

def toJson (p : Point3) : Lean.Json :=
  let jsonNumOrStr (x : Float) : Lean.Json :=
    match Lean.JsonNumber.fromFloat? x with
    | .inr n => Lean.Json.num n
    | .inl s => Lean.Json.str s
  Lean.Json.mkObj
    [ ("x", jsonNumOrStr p.x)
    , ("y", jsonNumOrStr p.y)
    , ("z", jsonNumOrStr p.z)
    ]

end Point3

/-- Helix parameterization. `step` controls angular spacing; `pitch` controls z growth per radian. -/
def helix (t : Float) (pitch : Float := 0.15) : Point3 :=
  { x := Float.cos t
    y := Float.sin t
    z := pitch * t
  }

/-- Embed `count` steps (inclusive endpoints: `count+1` points) along a helix. -/
def embedSteps (count : Nat) (step : Float := 0.35) (pitch : Float := 0.15) : List Point3 :=
  (List.range (count + 1)).map (fun k => helix (step * Float.ofNat k) pitch)

end IteratedVirtual
end HeytingLean

