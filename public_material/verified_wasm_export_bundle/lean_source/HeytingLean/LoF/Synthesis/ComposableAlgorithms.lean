import HeytingLean.LoF.Synthesis.Composable

/-!
# Synthesis.ComposableAlgorithms

Baseline (currently trivial) algorithms for producing `Synthesis.Decomposition` values.

The main `Composable` module is intentionally interface-first: it specifies what a quotient/residual
decomposition *is* and what it means to be sound. This file provides a minimal constructor so
downstream code can depend on a concrete `decompose` function today, while leaving
anti-unification / residualization heuristics to future work.
-/

namespace HeytingLean
namespace LoF
namespace Synthesis

open HeytingLean.ProgramCalculus

/-- A trivial decomposition: take the original program as the quotient and ignore the residual. -/
def trivialDecomposition (language : Language) (p : language.Program) : Decomposition language :=
  { original := p
    quotient := p
    residual := p
    recombine := fun q _r => q
    sound := by
      intro input
      rfl }

end Synthesis
end LoF
end HeytingLean

