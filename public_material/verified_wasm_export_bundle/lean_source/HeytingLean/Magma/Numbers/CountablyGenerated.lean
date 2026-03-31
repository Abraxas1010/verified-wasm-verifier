import HeytingLean.Magma.Numbers.Ordinal

namespace HeytingLean.Magma.Numbers

open HeytingLean.Magma

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A] [PairEncoding A] [ProductEncoding A]
  [NaturalPresentation A] [OrdinalPresentation A]

def CountablyGenerated (x : Magma A) : Prop :=
  ∃ f : ℕ → Magma A, ∀ n, f n ≤ x

def HasCountableRangePresentation (x : Magma A) : Prop :=
  ∃ (a₀ a₁ : A) (h : Incomparable a₀ a₁),
    ∃ f : ℕ → Magma A,
      ∀ n, magmatic_pair a₀ a₁ h (mnat_alt (A := A) n) (f n) ≤ x

class CountableGenerationPresentation (A : Type*) [MagmaticAtoms A] [MagmaticUniverse A]
    [PairEncoding A] [ProductEncoding A] [NaturalPresentation A] [OrdinalPresentation A] where
  countably_generated_is_range :
    ∀ {x : Magma A}, CountablyGenerated x → HasCountableRangePresentation (A := A) x

variable [CountableGenerationPresentation A]

theorem countably_generated_is_range (x : Magma A) (h : CountablyGenerated x) :
    HasCountableRangePresentation (A := A) x :=
  CountableGenerationPresentation.countably_generated_is_range h

end HeytingLean.Magma.Numbers
