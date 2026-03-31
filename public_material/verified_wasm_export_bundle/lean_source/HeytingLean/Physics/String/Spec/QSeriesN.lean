/-!
Spec (proof‑friendly) Q‑series with natural coefficients.
This parallels the Float‑based runtime structures but uses `Nat`
so that nonnegativity and similar properties are immediate.
-/

namespace HeytingLean
namespace Physics
namespace String
namespace Spec

structure QSeriesN where
  coeffs : List Nat
deriving Repr

namespace QSeriesN

@[simp] def length (q : QSeriesN) : Nat := q.coeffs.length

@[simp] def coeffAt (q : QSeriesN) (i : Nat) : Nat :=
  q.coeffs.getD i 0

@[simp] def zero (n : Nat) : QSeriesN := { coeffs := List.replicate n 0 }

@[simp] def bump (q : QSeriesN) (i : Nat) : QSeriesN :=
  match q.coeffs.splitAt i with
  | (pre, x :: post) => { coeffs := pre ++ (x.succ :: post) }
  | (pre, [])       => { coeffs := pre ++ [1] }

@[simp] def fromWeights (weights : List Nat) : QSeriesN :=
  weights.foldl (fun q w => QSeriesN.bump q w) (zero (weights.foldl Nat.max 0 + 1))

/-- Basic nonnegativity facts: casting coefficients to `Int` preserves nonnegativity. -/
@[simp] theorem coeffAt_nonneg (q : QSeriesN) (i : Nat) :
    (0 : Int) ≤ (coeffAt q i : Int) := by
  -- This is immediate since `coeffAt q i` is a natural number.
  simp [coeffAt]

@[simp] theorem fromWeights_nonneg (ws : List Nat) (i : Nat) :
    (0 : Int) ≤ (coeffAt (fromWeights ws) i : Int) := by
  simp

end QSeriesN

end Spec
end String
end Physics
end HeytingLean
