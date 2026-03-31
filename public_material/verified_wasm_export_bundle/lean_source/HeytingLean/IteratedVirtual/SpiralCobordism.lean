import HeytingLean.IteratedVirtual.VirtualComposition
import HeytingLean.IteratedVirtual.Spiral

/-!
# IteratedVirtual.SpiralCobordism

A lightweight “geometry view” of cobordism data:

- **xy**: position on a unit circle (one point per cobordism in a chain, plus the start point)
- **z**: the iteration level `k`

This is an *observation/visualization map*; it does not attempt to be faithful to any specific
geometric semantics beyond the “stacked circles” intuition.
-/

namespace HeytingLean
namespace IteratedVirtual

open CategoryTheory

namespace Point3

def helixAtLevel (level : Nat) (t : Float) : Point3 :=
  { x := Float.cos t
    y := Float.sin t
    z := Float.ofNat level
  }

end Point3

namespace CobordismChain

universe u v

variable {C : Type u} [Category.{v} C]

def embedAtLevel {X Y : C} {n : Nat} {A B : IteratedCellOver (C := C) X Y n}
    (level : Nat) (p : CobordismChain (C := C) A B) (step : Float := 0.35) : List Point3 :=
  (List.range (p.length + 1)).map (fun i => Point3.helixAtLevel level (step * Float.ofNat i))

end CobordismChain

end IteratedVirtual
end HeytingLean

