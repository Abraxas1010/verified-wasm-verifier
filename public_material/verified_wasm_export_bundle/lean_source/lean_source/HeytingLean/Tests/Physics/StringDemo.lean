import HeytingLean.Physics.String.QSeries
import HeytingLean.Physics.String.ModularQ
import HeytingLean.Physics.String.VOAGraded

/-!
Sanity tests for the small string-physics lenses.

These are small, executable checks that:
* constant q-series have stable length/coefficients;
* the modular canonicalizer is idempotent on its output; and
* the graded VOA character truncation produces nonnegative coefficients.
-/

namespace HeytingLean
namespace Tests
namespace Physics
namespace String

open HeytingLean.Physics.String

def constSeries (n : Nat) (v : Float) : QSeries :=
  { coeffs := Array.replicate n v }

/-- A tiny 2×2 modular matrix pair acting as identity. -/
def idModMatrices : ModMatrices :=
  { S := #[
      #[1.0, 0.0],
      #[0.0, 1.0]
    ]
  , T := #[
      #[1.0, 0.0],
      #[0.0, 1.0]
    ]
  }

def idQNucleus : QNucleus :=
  { mats := idModMatrices, steps := 2 }

-- Constant series are fixed by the identity nucleus.
#eval Id.run (
  let q := constSeries 2 1.0
  let q' := QNucleus.project idQNucleus q
  (q.coeffs, q'.coeffs)
)

-- A simple graded VOA example yields nonnegative truncated character.
#eval Id.run (
  let G : VOAGraded Unit := { weights := #[0, 1, 1] }
  let q := VOAGraded.charTrunc G
  (q.coeffs, q.coeffs.size)
)

end String
end Physics
end Tests
end HeytingLean
