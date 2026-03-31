import HeytingLean.Probability.Discrete

/-!
Build distributions from samples (finite arrays) using naive counting.
Requires `DecidableEq α` to group identical outcomes.
-/

namespace HeytingLean
namespace Probability

open HeytingLean.Math

private def insertCount {α} [DecidableEq α] (a : α) (xs : List (α × Nat)) : List (α × Nat) :=
  match xs with
  | [] => [(a,1)]
  | (b,n) :: tl => if a = b then (b, n+1) :: tl else (b,n) :: insertCount a tl

noncomputable def fromSamples {α} [DecidableEq α] [Inhabited α] (xs : Array α) : Dist α :=
  let idxs := List.range xs.size
  let counts := idxs.foldl (fun acc i => insertCount xs[i]! acc) ([] : List (α × Nat))
  let supp := counts.map (·.fst)
  let ws   := counts.map (fun p => (p.snd : ℝ))
  { support := supp.toArray, weights := ProbVec.normalizeR ws.toArray }

end Probability
end HeytingLean
