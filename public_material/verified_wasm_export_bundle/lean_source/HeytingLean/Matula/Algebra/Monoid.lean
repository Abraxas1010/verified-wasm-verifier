import HeytingLean.Matula.Core.Encoding

namespace HeytingLean
namespace Matula
namespace Algebra

/-- Positive naturals used by the Matula algebra layer. -/
abbrev PosNat := { n : Nat // 0 < n }

namespace PosNat

def one : PosNat := ⟨1, Nat.succ_pos 0⟩

def mul (a b : PosNat) : PosNat :=
  ⟨a.1 * b.1, Nat.mul_pos a.2 b.2⟩

instance : One PosNat := ⟨one⟩
instance : Mul PosNat := ⟨mul⟩

@[simp] theorem one_val : (1 : PosNat).1 = 1 := rfl
@[simp] theorem mul_val (a b : PosNat) : (a * b).1 = a.1 * b.1 := rfl

@[simp] theorem one_mul (a : PosNat) : 1 * a = a := by
  apply Subtype.ext
  simp

@[simp] theorem mul_one (a : PosNat) : a * 1 = a := by
  apply Subtype.ext
  simp

@[simp] theorem mul_assoc (a b c : PosNat) : (a * b) * c = a * (b * c) := by
  apply Subtype.ext
  simp [Nat.mul_assoc]

@[simp] theorem mul_comm (a b : PosNat) : a * b = b * a := by
  apply Subtype.ext
  simp [Nat.mul_comm]

/-- Total embedding `Nat → PosNat` by adding one. -/
def ofNat (n : Nat) : PosNat := ⟨n + 1, Nat.succ_pos n⟩

/--
Encode a rooted tree as a positive natural in the algebra lane.

This is intended to preserve the Matula code directly; the fallback branch only
handles the unreachable `matula t = 0` case defensively.
-/
def fromTree (t : RTree) : PosNat :=
  if h : matula t = 0 then
    1
  else
    ⟨matula t, Nat.pos_of_ne_zero h⟩

@[simp] theorem fromTree_val (t : RTree) :
    (fromTree t).1 = if matula t = 0 then 1 else matula t := by
  by_cases h : matula t = 0
  · simp [fromTree, h]
  · simp [fromTree, h]

theorem fromTree_val_of_matula_pos (t : RTree) (h : 0 < matula t) :
    (fromTree t).1 = matula t := by
  simp [fromTree, Nat.ne_of_gt h]

/-- Multiplicative transport on encoded trees. -/
def combineEncoded (t u : RTree) : PosNat :=
  fromTree t * fromTree u

@[simp] theorem combineEncoded_comm (t u : RTree) :
    combineEncoded t u = combineEncoded u t := by
  simp [combineEncoded, mul_comm]

end PosNat

end Algebra
end Matula
end HeytingLean
