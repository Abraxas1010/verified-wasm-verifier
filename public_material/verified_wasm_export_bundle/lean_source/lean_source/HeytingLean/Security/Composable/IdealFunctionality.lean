/-!
# Universal Composability (UC), interface-first: ideal functionalities and protocols

This is a lightweight UC-shaped interface intended for later refinement.
In particular, it does **not** commit to:
- a probability framework,
- computational indistinguishability,
- or a concrete scheduling/network semantics.
-/

namespace HeytingLean
namespace Security
namespace Composable

universe u v w

/-- An ideal functionality `F` takes an input and produces an output, plus some leakage. -/
structure IdealFunctionality where
  Input : Type u
  Output : Type v
  Leakage : Type w
  compute : Input → Output × Leakage

/-- A (single-shot) protocol in the real world, attempting to realize an ideal functionality. -/
structure Protocol (F : IdealFunctionality.{u, v, w}) where
  State : Type
  Message : Type
  init : State
  execute : F.Input → State → (F.Output × Message × State)

end Composable
end Security
end HeytingLean

