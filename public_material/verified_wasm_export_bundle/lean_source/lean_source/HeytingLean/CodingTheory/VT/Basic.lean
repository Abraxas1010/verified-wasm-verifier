import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import HeytingLean.CodingTheory.Hamming.Basic
import HeytingLean.CodingTheory.InsDel.Operations

namespace HeytingLean
namespace CodingTheory
namespace VT

/-!
# Varshamov–Tenengolts (VT) codes
-/

open HeytingLean.CodingTheory.Hamming

abbrev Bit := Hamming.Bit

def numIs : List Bit → Nat
| [] => 0
| x :: xs => numIs xs + (if x = 1 then 1 else 0)

def moment : List Bit → Nat
| [] => 0
| x :: xs => moment xs + numIs (x :: xs)

prefix:25 "ρ" => moment

def vtCode (n a m : Nat) : Set (List Bit) :=
  {X | X.length = n ∧ (ρ X) % m = a % m ∧ n + 1 ≤ m}

lemma vtCode_mem_iff {n a m : Nat} {X : List Bit} :
    X ∈ vtCode n a m ↔ X.length = n ∧ (ρ X) % m = a % m ∧ n + 1 ≤ m := by
  rfl

def sDel {α : Type _} (xs : List α) (n : Nat) : List α :=
  HeytingLean.CodingTheory.InsDel.sDel xs n
def sIns {α : Type _} (xs : List α) (n : Nat) (a : α) : List α :=
  HeytingLean.CodingTheory.InsDel.sIns xs n a

end VT
end CodingTheory
end HeytingLean
