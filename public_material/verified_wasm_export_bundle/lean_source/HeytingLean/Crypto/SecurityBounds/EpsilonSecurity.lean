import Mathlib.Data.Real.Basic

/-!
# ε-security (interface-first)

We model "ε-security" as an abstract claim that a protocol satisfies a security predicate with
distinguishing advantage bounded by `ε`.
-/

namespace HeytingLean
namespace Crypto
namespace SecurityBounds

/-- ε-security: a protocol satisfies a security predicate with advantage ≤ ε. -/
structure EpsilonSecure (Protocol : Type*) where
  epsilon : ℝ
  epsilon_nonneg : 0 ≤ epsilon
  secure : Protocol → Prop

end SecurityBounds
end Crypto
end HeytingLean

