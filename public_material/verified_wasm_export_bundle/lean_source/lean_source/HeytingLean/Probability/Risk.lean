import HeytingLean.Probability.Discrete

/-!
Risk measures for discrete distributions (finite support):
- mean (alias of expect with identity)
- variance: E[X^2] - (E[X])^2
- CVaR_α (discrete worst-α-tail average). Interprets larger values as worse.
All functions are executable-first and rely on simple list/array folds.
-/

namespace HeytingLean
namespace Probability

open HeytingLean.Math

noncomputable def mean (d : Dist ℝ) : ℝ :=
  Dist.expect d (fun x => x)

noncomputable def secondMoment (d : Dist ℝ) : ℝ :=
  Dist.expect d (fun x => x * x)

noncomputable def variance (d : Dist ℝ) : ℝ :=
  let m := mean d
  secondMoment d - m * m

/-!
Discrete CVaR (Conditional Value at Risk) at level α ∈ (0,1].
Interpretation: expected value in the worst α-tail (higher x is worse).
Implementation sorts support by value descending and averages the top α mass.
-/
noncomputable def cvar (d : Dist ℝ) (α : ℝ) : ℝ :=
  let n := d.support.size
  if α ≤ 0 then 0
  else
    let idxs := (List.range n)
    let pairs : List (ℝ × ℝ) := idxs.map (fun i => (d.support[i]!, d.weights.get! i))
    -- sort by value descending
    let sorted := pairs.mergeSort (fun p q => p.fst > q.fst)
    let rec go (ps : List (ℝ × ℝ)) (mass : ℝ) (acc : ℝ) : ℝ :=
      match ps with
      | [] => if mass = 0 then 0 else acc / mass
      | (x,w) :: tl =>
          if mass + w ≤ α then go tl (mass + w) (acc + x * w)
          else
            let need := α - mass
            let acc' := acc + x * need
            acc' / α
    go sorted 0 0

/-! Generalized CVaR by a scoring function on outcomes.
    For arbitrary α-type distributions, score : α → ℝ selects the risk metric. -/
noncomputable def cvarBy {α} [Inhabited α] (score : α → ℝ) (d : Dist α) (αLevel : ℝ) : ℝ :=
  let n := d.support.size
  if αLevel ≤ 0 then 0 else
    let idxs := (List.range n)
    let pairs : List (ℝ × ℝ) := idxs.map (fun i => (score d.support[i]!, d.weights.get! i))
    let sorted := pairs.mergeSort (fun p q => p.fst > q.fst)
    let rec go (ps : List (ℝ × ℝ)) (mass : ℝ) (acc : ℝ) : ℝ :=
      match ps with
      | [] => if mass = 0 then 0 else acc / mass
      | (x,w) :: tl =>
          if mass + w ≤ αLevel then go tl (mass + w) (acc + x * w)
          else
            let need := αLevel - mass
            let acc' := acc + x * need
            acc' / αLevel
    go sorted 0 0

noncomputable def meanBy {α} [Inhabited α] (score : α → ℝ) (d : Dist α) : ℝ :=
  Dist.expect d score

noncomputable def varianceBy {α} [Inhabited α] (score : α → ℝ) (d : Dist α) : ℝ :=
  let m := meanBy score d
  Dist.expect d (fun a => let x := score a; x * x) - m * m

end Probability
end HeytingLean
