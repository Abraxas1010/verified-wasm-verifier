import HeytingLean.Crypto.Lattice.VirtualReductionChain

/-!
# Tests.Crypto.VirtualReductionChainSanity

Compile-only checks for heterogeneous reduction chains.
-/

namespace HeytingLean.Tests.Crypto

open HeytingLean.Crypto.Lattice

universe u

variable {S₁ : Type u} {S₂ : Type u}
variable (V₁ : RecoveryView S₁) (V₂ : RecoveryView S₂)

def anyV₁ : AnyRecoveryView := ⟨S₁, V₁⟩
def anyV₂ : AnyRecoveryView := ⟨S₂, V₂⟩

#check AnyReductionChain.Chain (V := anyV₁ (V₁ := V₁)) (W := anyV₂ (V₂ := V₂))
#check AnyReductionChain.compile

end HeytingLean.Tests.Crypto

