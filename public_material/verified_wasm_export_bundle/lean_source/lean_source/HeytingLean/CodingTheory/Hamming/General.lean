import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import HeytingLean.CodingTheory.Hamming.Basic

namespace HeytingLean
namespace CodingTheory
namespace Hamming

/-!
# General Hamming parity-check (length 2^m - 1)
-/

def bit (n k : Nat) : Bit :=
  if Nat.testBit n k then 1 else 0

def hammingLength (m : Nat) : Nat := 2^m - 1

def hammingSyndrome (m : Nat) (x : BitVec (hammingLength m)) : BitVec m := fun k =>
  Finset.univ.sum fun i : Fin (hammingLength m) =>
    bit (i.1 + 1) k.1 * x i

def hammingCode (m : Nat) : Set (BitVec (hammingLength m)) :=
  {x | ∀ k : Fin m, hammingSyndrome m x k = 0}

end Hamming
end CodingTheory
end HeytingLean
