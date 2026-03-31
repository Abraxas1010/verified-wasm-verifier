/-!
# Fourier series on the torus (signatures)

This module declares lightweight signatures for Fourier series on ℝ/ℤ and
truncated reconstruction. Heavy proofs are intentionally omitted here to keep
the executable path lean.
-/

namespace HeytingLean
namespace Analysis
namespace SeriesTorus

structure Coeffs where
  -- Coefficient storage; complex coeffs as (Re,Im)
  coeffs : Array (Int × Float × Float)  -- (n, Re, Im)
deriving Repr

def truncate (θ : Nat) (c : Coeffs) : Coeffs :=
  { coeffs := c.coeffs.filter (fun p => (p.fst.natAbs:Nat) ≤ θ) }

def reconstructTrunc (θ : Nat) (c : Coeffs) (xs : Array Float) : Array Float := Id.run do
  -- very simple reconstruction: ignore phases, sum real parts for matching n
  let cs := (truncate θ c).coeffs
  let mut out := Array.replicate xs.size 0.0
  for i in [0:xs.size] do
    let mut s : Float := 0.0
    for p in cs do
      let (_, re, _) := p
      s := s + re
    out := out.set! i s
  return out

end SeriesTorus
end Analysis
end HeytingLean
