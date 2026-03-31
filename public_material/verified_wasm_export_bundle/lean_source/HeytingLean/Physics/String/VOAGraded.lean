import HeytingLean.Physics.String.QSeries
import HeytingLean.Physics.String.CFT

/-
Graded VOA scaffold: weights and truncation into a q-series.

We provide a helper to build a truncated character from a finite multiset
of L0-weights by counting occurrences per degree. This remains a finite,
executable model for demos and tests, not a full VOA formalization.
-/

namespace HeytingLean
namespace Physics
namespace String

open HeytingLean.Physics.String

structure VOAGraded (V : Type u) where
  weights : Array Nat
deriving Repr

namespace VOAGraded

@[simp] def charTrunc (G : VOAGraded V) : QSeries := Id.run do
  let maxd := G.weights.foldl (init := 0) Nat.max
  let mut coeffs : Array Float := Array.replicate (maxd+1) 0.0
  for w in G.weights do
    coeffs := coeffs.set! w (coeffs[w]! + 1.0)
  return { coeffs := coeffs }

/-- Package the truncated character of a graded VOA as a worldsheet CFT partition. -/
@[simp] def toCFT (G : VOAGraded V)
    (name : String) (centralCharge : Float) : WorldsheetCFT :=
  { name := name
    centralCharge := centralCharge
    partitionZ := (charTrunc G).coeffs }

/-- Coefficients of the induced CFT partition agree with the truncated VOA character. -/
  @[simp] theorem coeff_toCFT (G : VOAGraded V)
      (name : String) (centralCharge : Float) (i : Nat) :
      (toCFT G name centralCharge).coeff i =
        (charTrunc G).coeffAt i := by
  simp [toCFT, WorldsheetCFT.coeff, QSeries.coeffAt]

end VOAGraded

end String
end Physics
end HeytingLean
