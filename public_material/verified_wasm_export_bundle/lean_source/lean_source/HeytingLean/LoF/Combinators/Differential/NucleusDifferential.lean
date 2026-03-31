import Mathlib.LinearAlgebra.Finsupp.Defs
import HeytingLean.LoF.Combinators.Differential.VectorSpace

/-!
# Differential combinators: linear extension of a “nucleus-like” endomap on terms

HeytingLean's existing nucleus machinery lives on lattice/Heyting-algebra objects.
For differential experimentation on *syntax*, we often start from an endomap on terms
`R : Comb → Comb` (e.g. a closure/normalization heuristic) and extend it linearly to
formal sums.

This file provides that linear extension and a simple “support-level fixed point” projector.
-/

noncomputable section

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Differential

open scoped BigOperators

namespace FormalSum

variable {K : Type*} [CommSemiring K]

/-- Linear extension of an endomap on terms, via `Finsupp.mapDomain`. -/
noncomputable def nucleusLinear (R : LoF.Comb → LoF.Comb) : FormalSum K →ₗ[K] FormalSum K :=
  Finsupp.lmapDomain K K R

theorem nucleusLinear_idempotent (R : LoF.Comb → LoF.Comb) (h : ∀ t, R (R t) = R t) :
    (nucleusLinear (K := K) R).comp (nucleusLinear (K := K) R) = nucleusLinear (K := K) R := by
  have hfun : (fun t => R (R t)) = R := funext h
  -- Compose = mapDomain (R ∘ R), then rewrite by `hfun`.
  calc
    (nucleusLinear (K := K) R).comp (nucleusLinear (K := K) R)
        = Finsupp.lmapDomain K K (fun t => R (R t)) := by
            simpa [nucleusLinear, Function.comp] using
              (Finsupp.lmapDomain_comp (M := K) (R := K) (f := R) (g := R)).symm
    _ = nucleusLinear (K := K) R := by
          simpa [nucleusLinear] using congrArg (Finsupp.lmapDomain K K) hfun

/-- Term-level fixed points of an endomap `R`. -/
def termFixedPoints (R : LoF.Comb → LoF.Comb) : Set LoF.Comb :=
  { t | R t = t }

/-- Projection that drops all non-fixed terms from a formal sum. -/
def projectToFixed (R : LoF.Comb → LoF.Comb) (v : FormalSum K) : FormalSum K :=
  v.filter (fun t => R t = t)

end FormalSum

end Differential
end Combinators
end LoF
end HeytingLean

