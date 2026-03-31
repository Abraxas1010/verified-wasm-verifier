import HeytingLean.Math.ProbVec

/-!
Discrete distributions over finite support (executable-first).
- `Dist α` stores an array of outcomes and a probability vector of same length.
- Builders from weighted pairs with normalization.
- `pmf`, `map`, `bind`, `prod`, `expect` (on ℝ-valued functions).
-/

namespace HeytingLean
namespace Probability

open HeytingLean.Math

structure Dist (α : Type u) where
  support : Array α
  weights : ProbVec

namespace Dist

variable {α β : Type u}

private def bindList {σ τ} (xs : List σ) (f : σ → List τ) : List τ :=
  xs.foldr (fun a acc => f a ++ acc) []

@[simp] def length (d : Dist α) : Nat := d.support.size

@[simp] noncomputable def fromPairs (xs : Array (α × ℝ)) : Dist α :=
  let supp := xs.map (·.fst)
  let ws   := ProbVec.normalizeR (xs.map (·.snd))
  { support := supp, weights := ws }

@[simp] noncomputable def uniform (xs : Array α) : Dist α :=
  { support := xs, weights := ProbVec.normalizeR (Array.replicate xs.size (1 : ℝ)) }

def pmf [DecidableEq α] [Inhabited α] (d : Dist α) (a : α) : ℝ :=
  -- sum weights where support equals a (linear scan; finite support)
  let pairs := (List.range d.support.size).map (fun i => (d.support[i]!, d.weights.get! i))
  let contribs := pairs.filterMap (fun (p : α × ℝ) => if p.fst = a then some p.snd else none)
  HeytingLean.Math.ProbVec.sumList contribs

def map (f : α → β) (d : Dist α) : Dist β :=
  { support := d.support.map f, weights := d.weights }

noncomputable def bind [Inhabited α] (d : Dist α) (k : α → Dist β) : Dist β :=
  let idxs := List.range d.support.size
  let suppL : List β := bindList idxs (fun i => (k (d.support[i]!)).support.toList)
  let wsL   : List ℝ := bindList idxs (fun i =>
    let w := d.weights.get! i
    ((k (d.support[i]!)).weights.data.toList).map (fun x => x * w))
  { support := suppL.toArray, weights := ProbVec.normalizeR wsL.toArray }

noncomputable def prod [Inhabited α] [Inhabited β] (d₁ : Dist α) (d₂ : Dist β) : Dist (α × β) :=
  let i1 := List.range d₁.support.size
  let i2 := List.range d₂.support.size
  let suppL : List (α × β) := bindList i1 (fun i => i2.map (fun j => (d₁.support[i]!, d₂.support[j]!)))
  let wsL   : List ℝ := bindList i1 (fun i =>
     let wa := d₁.weights.get! i
     i2.map (fun j => wa * d₂.weights.get! j))
  { support := suppL.toArray, weights := ProbVec.normalizeR wsL.toArray }

noncomputable def expect [Inhabited α] (d : Dist α) (f : α → ℝ) : ℝ :=
  let idxs := List.range d.support.size
  let vals := idxs.map (fun i => f d.support[i]!)
  let ws   := idxs.map (fun i => d.weights.get! i)
  HeytingLean.Math.ProbVec.sumList ((List.zipWith (· * ·) vals ws))

/-! Coalesce duplicate outcomes by summing their weights; optional trim of tiny masses. -/
noncomputable def canonicalize [Inhabited α] [DecidableEq α] (d : Dist α) (trimTol : ℝ := 0) : Dist α :=
  let idxs := List.range d.support.size
  let pairs : List (α × ℝ) := idxs.map (fun i => (d.support[i]!, d.weights.get! i))
  let rec insert (a : α) (w : ℝ) (xs : List (α × ℝ)) : List (α × ℝ) :=
    match xs with
    | [] => [(a,w)]
    | (b,u) :: tl => if a = b then (b,u+w) :: tl else (b,u) :: insert a w tl
  let folded := pairs.foldl (fun acc p => insert p.fst p.snd acc) []
  let filtered := folded.filter (fun p => p.snd > trimTol)
  { support := filtered.map (·.fst) |>.toArray, weights := ProbVec.normalizeR (filtered.map (·.snd) |>.toArray) }

noncomputable def mapCoalesce [Inhabited β] [DecidableEq β] (f : α → β) (d : Dist α) (trimTol : ℝ := 0) : Dist β :=
  canonicalize (map f d) trimTol

noncomputable def bindCoalesce [Inhabited α] [Inhabited β] [DecidableEq β]
    (d : Dist α) (k : α → Dist β) (trimTol : ℝ := 0) : Dist β :=
  canonicalize (bind d k) trimTol

end Dist

end Probability
end HeytingLean
