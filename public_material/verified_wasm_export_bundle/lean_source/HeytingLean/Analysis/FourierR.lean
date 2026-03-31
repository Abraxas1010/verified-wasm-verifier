/-!
# Fourier on ℝᵈ (signatures)

This module provides signatures/records to stage a Fourier transform on ℝᵈ.
It intentionally avoids integrals/proofs to keep strict builds fast.
-/

namespace HeytingLean
namespace Analysis
namespace FourierR

structure Space where
  dim : Nat := 1
deriving Repr

structure Pair where
  X    : Space
  note : String := "staged"
deriving Repr

def unit (X : Space) : Pair := { X, note := "unitary signature (staged)" }

end FourierR
end Analysis
end HeytingLean

