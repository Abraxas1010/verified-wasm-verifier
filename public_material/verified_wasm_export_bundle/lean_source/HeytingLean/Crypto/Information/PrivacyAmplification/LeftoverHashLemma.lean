import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import HeytingLean.Crypto.Information.Hashing

/-!
# Leftover Hash Lemma (interface-first)

We provide:
- finite/discrete definitions of statistical distance and uniform distributions; and
- a *packaged* Leftover Hash Lemma statement, as a structure field.

This keeps the bundle free of proof placeholders while making the dependency explicit.
-/

namespace HeytingLean
namespace Crypto
namespace Information
namespace PrivacyAmplification

open scoped BigOperators

namespace Finite

/-- Statistical distance on finite spaces (for raw `α → ℝ` pmf-like functions). -/
noncomputable def statDistance {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1 / 2) * ∑ x : α, |p x - q x|

/-- Uniform "distribution" on a finite type. -/
noncomputable def uniform {α : Type*} [Fintype α] : α → ℝ :=
  fun _ => 1 / (Fintype.card α)

/-- Product distribution on a product type. -/
noncomputable def productDist {α β : Type*} (p : α → ℝ) (q : β → ℝ) : α × β → ℝ :=
  fun (a, b) => p a * q b

/-- Uniform seed distribution on a finite seed type. -/
noncomputable def seedDist {S : Type*} [Fintype S] : S → ℝ :=
  uniform

/-- Joint distribution of `(seed, hash(seed, X))` for a finite `X : D → ℝ`. -/
noncomputable def jointDist {D R S : Type*} [Fintype D] [Fintype S] [DecidableEq R]
    (H : HeytingLean.Crypto.Information.Hashing.HashFamily D R S)
    (X : D → ℝ) : S × R → ℝ :=
  fun (s, r) =>
    seedDist (S := S) s * ∑ x : D, (if H.hash s x = r then X x else 0)

end Finite

open HeytingLean.Crypto.Information.Hashing

/-- A packaged (interface) Leftover Hash Lemma statement for finite spaces. -/
structure LeftoverHashLemma (D R S : Type*)
    [Fintype D] [Fintype R] [Fintype S] [DecidableEq R] [TwoUniversal D R S] where
  /-- A chosen min-entropy function on finite distributions (bits). -/
  minEntropy : (D → ℝ) → ℝ
  /-- The LHL statement (as an assumption packaged here). -/
  lhl :
      ∀ (X : D → ℝ),
        (∀ x, 0 ≤ X x) →
        (∑ x : D, X x = 1) →
        ∀ (k : ℝ),
          k ≤ minEntropy X →
          let ℓ : ℝ := Real.log (Fintype.card R) / Real.log 2
          let ε : ℝ := Real.rpow 2 (-(k - ℓ) / 2)
          Finite.statDistance
              (Finite.jointDist (R := R)
                (H := (TwoUniversal.toHashFamily (D := D) (R := R) (S := S))) X)
              (Finite.productDist (Finite.seedDist (S := S)) (Finite.uniform (α := R))) ≤ ε

end PrivacyAmplification
end Information
end Crypto
end HeytingLean

