import Mathlib.Data.Int.Init
import HeytingLean.Topology.Knot.BracketMathlib
import HeytingLean.Topology.Knot.Reidemeister

/-!
# Knot theory: Jones normalisation (Mathlib proof layer)

`HeytingLean.Topology.Knot.Jones` provides an executable Jones-style normalisation using the
executable `LaurentPoly`. For theorem proving we use the Mathlib-valued bracket
`HeytingLean.Topology.Knot.Kauffman.bracketGraphML`.

This file defines the corresponding normalisation factor and a normalised bracket in the Mathlib
`LaurentPolynomial ℤ` layer.
-/

namespace HeytingLean
namespace Topology
namespace Knot

namespace Kauffman

open scoped LaurentPolynomial
open Reidemeister

noncomputable section

/-- Writhe (sum of crossing signs) for a sign array. -/
def writheML (sign : Array CurlKind) : Int :=
  sign.toList.foldl (fun acc k => acc + match k with | .pos => 1 | .neg => -1) 0

def normCoeffML (w : Int) : ℤ :=
  if w % 2 = 0 then 1 else -1

/-- The normalisation factor `(-A)^{-3w}` as a Laurent monomial (Mathlib layer). -/
def normFactorML (w : Int) : PolyML :=
  (normCoeffML w : PolyML) * LaurentPolynomial.T ((-3 : Int) * w)

/-- Normalised bracket (Jones-style), Mathlib Laurent polynomial layer.

This checks that the sign array length matches `g.n`, then multiplies `bracketGraphML g` by the
normalisation factor.
-/
def normalizedBracketML (g : PDGraph) (sign : Array CurlKind) : Except String PolyML := do
  if sign.size != g.n then
    throw s!"normalizedBracketML: sign array length {sign.size} (expected {g.n})"
  let b ← bracketGraphML g
  return normFactorML (writheML sign) * b

end

end Kauffman

end Knot
end Topology
end HeytingLean
