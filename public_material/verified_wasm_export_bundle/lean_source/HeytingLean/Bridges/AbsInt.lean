/-!
# Abstract Interpretation (Interval Demo) — α, γ, and Interior I

This minimal bridge provides a concrete abstract domain (Intervals over `Int`)
with a simple abstraction `α : Int → Interval`, concretization `γ : Interval → Int`
and an interior operator `I a := α (γ a)` on intervals. This is intentionally
lightweight and proof-free to keep the executable path fast.
-/

namespace HeytingLean
namespace Bridges
namespace AbsInt

structure Interval where
  lo : Int
  hi : Int
deriving Repr, DecidableEq

def α (c : Int) : Interval := { lo := c, hi := c }

def γ (a : Interval) : Int := a.lo

def I (a : Interval) : Interval := α (γ a)

end AbsInt
end Bridges
end HeytingLean
