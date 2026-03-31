import HeytingLean.LoF.Combinators.Differential.LinearComb
import Mathlib.Data.Finsupp.SMul

/-!
# Differential.PartialEvalDiff

Minimal glue between “specialization maps” on SKY terms and the Differential (formal-sum) layer.

The Differential slice models superpositions of terms via `FormalSum K := Comb →₀ K`. Given any
term-level map `f : Comb → Comb` (e.g. a specialization, normalization, or partial evaluator),
we can push it forward to formal sums by mapping basis terms and re-summing coefficients.

This file does **not** claim that specialization commutes with stepping/derivatives in general.
Instead it exposes:

* `FormalSum.mapComb` — the pushforward operation, and
* `CommutesWithSteps` — an explicit property you can require/prove for particular `f`.
-/

noncomputable section

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Differential

namespace FormalSum

variable {K : Type*} [Semiring K]

/-- Push a term-level map `f : Comb → Comb` forward to a map on formal sums. -/
def mapComb (f : LoF.Comb → LoF.Comb) (v : FormalSum K) : FormalSum K :=
  Finsupp.mapDomain f v

@[simp] theorem mapComb_finsupp_single (f : LoF.Comb → LoF.Comb) (t : LoF.Comb) (a : K) :
    mapComb (K := K) f (Finsupp.single t a) = Finsupp.single (f t) a := by
  classical
  simp [mapComb]

@[simp] theorem mapComb_single (f : LoF.Comb → LoF.Comb) (t : LoF.Comb) :
    mapComb (K := K) f (single (K := K) t) = single (K := K) (f t) := by
  classical
  simp [mapComb, single]

@[simp] theorem mapComb_zero (f : LoF.Comb → LoF.Comb) :
    mapComb (K := K) f (0 : FormalSum K) = 0 := by
  classical
  simp [mapComb]

/-- `mapComb` is additive. -/
theorem mapComb_add (f : LoF.Comb → LoF.Comb) (v w : FormalSum K) :
    mapComb (K := K) f (v + w) = mapComb (K := K) f v + mapComb (K := K) f w := by
  simpa [mapComb] using (Finsupp.mapDomain_add (f := f) (v₁ := v) (v₂ := w))

/-- `mapComb` commutes with scalar multiplication. -/
theorem mapComb_smul (f : LoF.Comb → LoF.Comb) (a : K) (v : FormalSum K) :
    mapComb (K := K) f (a • v) = a • mapComb (K := K) f v := by
  simpa [mapComb] using (Finsupp.mapDomain_smul (f := f) a v)

@[simp] theorem mapComb_id (v : FormalSum K) :
    mapComb (K := K) (fun t => t) v = v := by
  classical
  ext t
  simpa [mapComb] using
    (Finsupp.mapDomain_apply (f := fun t => t) (hf := fun _ _ h => h) (x := v) (a := t))

/-- A concrete commutation law that some specialization maps may satisfy. -/
structure CommutesWithSteps (f : LoF.Comb → LoF.Comb) : Prop where
  commutes : ∀ v : FormalSum K, mapComb (K := K) f (steps (K := K) v) = steps (K := K) (mapComb (K := K) f v)

theorem steps_add (v w : FormalSum K) :
    steps (K := K) (v + w) = steps (K := K) v + steps (K := K) w := by
  classical
  -- `steps` is defined as a `Finsupp.sum` with an additive kernel in the coefficient argument.
  simpa [steps] using
    (Finsupp.sum_add_index' (f := v) (g := w)
      (h := fun t a => a • stepSum (K := K) t)
      (by intro t; simp)
      (by intro t a₁ a₂; simp [add_smul]))

theorem commutesWithSteps_of_stepSum
    (f : LoF.Comb → LoF.Comb)
    (hStepSum : ∀ t : LoF.Comb, mapComb (K := K) f (stepSum (K := K) t) = stepSum (K := K) (f t)) :
    CommutesWithSteps (K := K) f := by
  classical
  refine ⟨?_⟩
  intro v
  refine Finsupp.induction v ?_ ?_
  · simp [steps, mapComb]
  · intro t a v ht ha hv
    -- Reduce to the basis commutation law using additivity/linearity of `steps` and `mapComb`.
    calc
      mapComb (K := K) f (steps (K := K) (Finsupp.single t a + v))
          = mapComb (K := K) f (steps (K := K) (Finsupp.single t a) + steps (K := K) v) := by
              simp [steps_add]
      _ = mapComb (K := K) f (steps (K := K) (Finsupp.single t a)) + mapComb (K := K) f (steps (K := K) v) := by
              simp [mapComb_add]
      _ = mapComb (K := K) f (steps (K := K) (Finsupp.single t a)) + steps (K := K) (mapComb (K := K) f v) := by
              simp [hv]
      _ = a • stepSum (K := K) (f t) + steps (K := K) (mapComb (K := K) f v) := by
              simp [steps, mapComb_smul, hStepSum]
      _ = steps (K := K) (Finsupp.single (f t) a) + steps (K := K) (mapComb (K := K) f v) := by
              simp [steps]
      _ = steps (K := K) (Finsupp.single (f t) a + mapComb (K := K) f v) := by
              symm
              exact steps_add (K := K) (v := Finsupp.single (f t) a) (w := mapComb (K := K) f v)
      _ = steps (K := K) (mapComb (K := K) f (Finsupp.single t a + v)) := by
              simp [mapComb_add]

theorem commutesWithSteps_id :
    CommutesWithSteps (K := K) (fun t => t) := by
  refine commutesWithSteps_of_stepSum (K := K) (f := fun t => t) ?_
  intro t
  simp

theorem mapComb_foldl_add_single {α : Type*} (f : LoF.Comb → LoF.Comb) (acc : FormalSum K)
    (l : List (α × LoF.Comb)) :
    mapComb (K := K) f (l.foldl (fun acc e => acc + Finsupp.single e.2 (1 : K)) acc) =
      l.foldl (fun acc e => acc + Finsupp.single (f e.2) (1 : K)) (mapComb (K := K) f acc) := by
  classical
  induction l generalizing acc with
  | nil =>
      simp [mapComb]
  | cons e l ih =>
      -- Unfold `foldl` and use the induction hypothesis on the tail with the updated accumulator.
      simp [List.foldl]
      have ih' := ih (acc := acc + Finsupp.single e.2 (1 : K))
      rw [mapComb_add (K := K) (f := f) (v := acc) (w := Finsupp.single e.2 (1 : K))] at ih'
      simp [mapComb_finsupp_single] at ih'
      exact ih'

theorem foldl_add_single_map_liftRightK (acc : FormalSum K) (l : List (LoF.Comb.EventData × LoF.Comb)) :
    (l.map (LoF.Comb.liftRight LoF.Comb.K)).foldl (fun acc e => acc + Finsupp.single e.2 (1 : K)) acc =
      l.foldl (fun acc e => acc + Finsupp.single (LoF.Comb.app LoF.Comb.K e.2) (1 : K)) acc := by
  classical
  induction l generalizing acc with
  | nil =>
      simp
  | cons e l ih =>
      simp [List.foldl, LoF.Comb.liftRight, ih]

theorem commutesWithSteps_appK :
    CommutesWithSteps (K := K) (fun t => LoF.Comb.app LoF.Comb.K t) := by
  classical
  refine commutesWithSteps_of_stepSum (K := K) (f := fun t => LoF.Comb.app LoF.Comb.K t) ?_
  intro t
  have hMap :
      mapComb (K := K) (fun u => LoF.Comb.app LoF.Comb.K u) (stepSum (K := K) t) =
        (LoF.Comb.stepEdgesList t).foldl
          (fun acc e => acc + Finsupp.single (LoF.Comb.app LoF.Comb.K e.2) (1 : K)) 0 := by
    -- Push `mapComb` through the `foldl` defining `stepSum`.
    simpa [stepSum] using
      (mapComb_foldl_add_single (K := K) (f := fun u => LoF.Comb.app LoF.Comb.K u)
        (acc := (0 : FormalSum K)) (l := LoF.Comb.stepEdgesList t))
  have hStep :
      stepSum (K := K) (LoF.Comb.app LoF.Comb.K t) =
        (LoF.Comb.stepEdgesList t).foldl
          (fun acc e => acc + Finsupp.single (LoF.Comb.app LoF.Comb.K e.2) (1 : K)) 0 := by
    -- One-step successors of `K · t` are exactly `K · u` for successors `u` of `t`.
    have hEdges :
        LoF.Comb.stepEdgesList (LoF.Comb.app LoF.Comb.K t) =
          (LoF.Comb.stepEdgesList t).map (LoF.Comb.liftRight LoF.Comb.K) := by
      simp [LoF.Comb.stepEdgesList, LoF.Comb.rootEdgesList, LoF.Comb.rootStep?]
    -- Rewrite `stepSum` along `hEdges`, then strip the `liftRight` map.
    simpa [stepSum, hEdges] using
      (foldl_add_single_map_liftRightK (K := K) (acc := (0 : FormalSum K)) (l := LoF.Comb.stepEdgesList t))
  calc
    mapComb (K := K) (fun u => LoF.Comb.app LoF.Comb.K u) (stepSum (K := K) t)
        = (LoF.Comb.stepEdgesList t).foldl
            (fun acc e => acc + Finsupp.single (LoF.Comb.app LoF.Comb.K e.2) (1 : K)) 0 := hMap
    _ = stepSum (K := K) (LoF.Comb.app LoF.Comb.K t) := by
          symm
          exact hStep

end FormalSum

end Differential
end Combinators
end LoF
end HeytingLean
