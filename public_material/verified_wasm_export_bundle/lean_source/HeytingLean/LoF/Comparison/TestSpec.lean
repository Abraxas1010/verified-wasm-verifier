import HeytingLean.LoF.ComparisonNucleus

/-!
CI/Test Spec for Comparison Nucleus

This tiny module provides a minimal Spec on the finite carrier used by the
prover (lists of ByteArray). It is identity by design and only intended to
exercise the comparison branch in CI without affecting production.
-/

namespace HeytingLean
namespace LoF
namespace Comparison
namespace TestSpec

abbrev L   := List ByteArray
abbrev Ωℓ := L

def f (s : L) : Ωℓ := s
def g (ω : Ωℓ) : L := ω

def SpecCI : Spec L Ωℓ :=
  { f := f, g := g, name := "ci_spec" }

end TestSpec
end Comparison
end LoF
end HeytingLean
