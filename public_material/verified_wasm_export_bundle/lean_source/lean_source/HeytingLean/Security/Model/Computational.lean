import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

namespace HeytingLean
namespace Security
namespace Model

/-!
# Computational security (foundations)

This is a lightweight, **definition-first** layer for computational security statements.

It intentionally does not fix a concrete game API (IND-CPA/IND-CCA/etc.); instead it provides:
- a negligible-function predicate (`Negligible`) based on Mathlib’s superpolynomial decay; and
- a minimal adversary record with a (separate) polynomial-time predicate.

Specific games (e.g. IND-CCA) live elsewhere (see `HeytingLean.Crypto.Games.*`) and can instantiate
these predicates later.
-/

namespace Computational

open Filter

/-- A standard negligible function `ℕ → ℝ` (superpolynomial decay) relative to `n ↦ (n : ℝ)`. -/
def Negligible (f : ℕ → ℝ) : Prop :=
  Asymptotics.SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ)) f

/-- A minimal computational adversary, tracked only by a running-time bound and an advantage curve. -/
structure Adversary where
  runtime : ℕ → ℕ
  advantage : ℕ → ℝ

/-- A simple polynomial-time predicate for the (reported) running time. -/
def PolyTime (A : Adversary) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, A.runtime n ≤ n ^ c + c

abbrev PPT (A : Adversary) : Prop :=
  PolyTime A

/-- A generic computational security statement for a given advantage function. -/
def Secure (Adv : Adversary → ℕ → ℝ) : Prop :=
  ∀ A, PPT A → Negligible (Adv A)

end Computational

end Model
end Security
end HeytingLean

