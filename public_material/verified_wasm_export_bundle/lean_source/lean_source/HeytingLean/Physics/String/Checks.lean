import HeytingLean.Physics.String.QSeries
import HeytingLean.Physics.String.ModularQ
import HeytingLean.Physics.String.VOAGraded

/-
Lightweight, executable-first checks for the small String modules.
These are not formal proofs; they provide quick guards usable in tests.
-/

namespace HeytingLean
namespace Physics
namespace String

@[simp] def nonnegFloatArray (xs : Array Float) : Bool := Id.run do
  let mut ok := true
  for i in [:xs.size] do
    if xs[i]! < 0.0 then ok := false
  return ok

@[simp] def charTruncNonneg (G : VOAGraded α) : Bool :=
  nonnegFloatArray (VOAGraded.charTrunc G).coeffs

@[simp] def projectIdemCheck (N : QNucleus) (q : QSeries) : Bool :=
  let q1 := QNucleus.project N q
  let q2 := QNucleus.project N q1
  toString q1.coeffs == toString q2.coeffs

/-- Canonicalization is no worse than immediate S/T moves (lexicographic). -/
@[simp] def projectNoWorse1 (N : QNucleus) (q : QSeries) : Bool :=
  let c := (QNucleus.project N q).coeffs
  let s := applyMat N.mats.S q.coeffs
  let t := applyMat N.mats.T q.coeffs
  lexico c s || lexico c t || (toString c == toString q.coeffs)

end String
end Physics
end HeytingLean
