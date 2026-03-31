import Mathlib.Data.Finsupp.Basic
import HeytingLean.LoF.Combinators.SKY

/-!
# Differential combinators: formal finite linear combinations

This file introduces `FormalSum K := Comb →₀ K`, i.e. finitely supported formal linear
combinations of SKY combinator terms.

This is a *library* layer (noncomputable in general, because Mathlib's `Finsupp.single` uses
classical choice to avoid requiring `DecidableEq` on coefficients).
-/

noncomputable section

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Differential

open scoped BigOperators

abbrev FormalSum (K : Type*) [Zero K] : Type _ :=
  LoF.Comb →₀ K

namespace FormalSum

variable {K : Type*} [Zero K]

def toList (v : FormalSum K) : List (LoF.Comb × K) :=
  v.support.toList.map (fun t => (t, v t))

end FormalSum

def single {K : Type*} [Zero K] [One K] (t : LoF.Comb) : FormalSum K :=
  Finsupp.single t 1

namespace FormalSum

variable {K : Type*} [Semiring K]

def dot (v w : FormalSum K) : K :=
  v.sum (fun t a => a * w t)

def l2NormSq (v : FormalSum K) : K :=
  dot v v

end FormalSum

end Differential
end Combinators
end LoF
end HeytingLean
