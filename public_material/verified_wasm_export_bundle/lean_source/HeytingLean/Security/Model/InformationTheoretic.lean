import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import HeytingLean.Probability.InfoTheory.FinDist

namespace HeytingLean
namespace Security
namespace Model

/-!
# Information-theoretic security (foundations)

We model finite distributions using `HeytingLean.Probability.InfoTheory.FinDist` (a proof-first,
real-valued PMF with nonnegativity and normalization).

This file provides:
- total-variation style statistical distance for `FinDist`;
- simple perfect-secrecy predicates for randomized encryption.
-/

namespace InformationTheoretic

open scoped BigOperators

open HeytingLean.Probability.InfoTheory

/-- Statistical distance between two finite distributions (total variation / 2 form). -/
noncomputable def statisticalDistance {α : Type u} [Fintype α] (P Q : FinDist α) : ℝ :=
  (1 / 2 : ℝ) * ∑ a : α, |P.pmf a - Q.pmf a|

/-- Randomized encryption as a (finite) ciphertext distribution for each message. -/
abbrev RandomizedEnc (M C : Type u) [Fintype C] :=
  M → FinDist C

/-- Perfect secrecy: ciphertext distributions do not depend on the message. -/
def perfectSecrecy {M C : Type u} [Fintype C] (enc : RandomizedEnc M C) : Prop :=
  ∀ m₀ m₁ : M, ∀ c : C, (enc m₀).pmf c = (enc m₁).pmf c

/-- Statistical indistinguishability in terms of a concrete (non-asymptotic) bound `ε`. -/
def statIndistinguishable {M C : Type u} [Fintype C]
    (enc : RandomizedEnc M C) (ε : ℝ) : Prop :=
  ∀ m₀ m₁ : M,
    statisticalDistance (P := enc m₀) (Q := enc m₁) ≤ ε

end InformationTheoretic

end Model
end Security
end HeytingLean
