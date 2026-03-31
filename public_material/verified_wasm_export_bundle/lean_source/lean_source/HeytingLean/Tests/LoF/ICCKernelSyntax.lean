import HeytingLean.LoF.ICCKernel.Semantics

namespace HeytingLean
namespace Tests
namespace LoF
namespace ICCKernelSyntax

open HeytingLean.LoF.ICCKernel

def sampleTerm : Term :=
  .lam (.str .anonymous "x") .default (.sort .zero) (.bvar 0)

example : Term.size sampleTerm = 3 := by
  rfl

example : Term.closedAbove 0 sampleTerm := by
  simp [sampleTerm, Term.closedAbove]

example : Term.containsFallbackMarker sampleTerm = false := by
  rfl

end ICCKernelSyntax
end LoF
end Tests
end HeytingLean
