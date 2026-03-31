import HeytingLean.LeanSP.Arith.Word256
import HeytingLean.LeanSP.Arith.SignedArith

/-!
# LeanSP.Arith.Word256Props

Proved properties of EVM Word256 arithmetic. All proofs closed.
-/

namespace LeanSP.Arith

theorem add_comm (a b : Word256) : add a b = add b a := by
  unfold add; exact BitVec.add_comm a b

theorem mul_comm (a b : Word256) : mul a b = mul b a := by
  unfold mul; exact BitVec.mul_comm a b

theorem add_assoc (a b c : Word256) : add (add a b) c = add a (add b c) := by
  unfold add; exact BitVec.add_assoc a b c

theorem sub_self (a : Word256) : sub a a = Word256.zero := by
  unfold sub Word256.zero
  simp [BitVec.sub_self]

theorem div_zero (a : Word256) : div a Word256.zero = Word256.zero := by
  unfold div
  simp [Word256.zero]

theorem mod_zero (a : Word256) : mod a Word256.zero = Word256.zero := by
  unfold mod
  simp [Word256.zero]

theorem addmod_zero_n (a b : Word256) : addmod a b Word256.zero = Word256.zero := by
  unfold addmod
  simp [Word256.zero]

theorem mulmod_zero_n (a b : Word256) : mulmod a b Word256.zero = Word256.zero := by
  unfold mulmod
  simp [Word256.zero]

theorem isZero_zero : isZero Word256.zero = Word256.one := by
  unfold isZero
  simp [Word256.zero]

theorem isZero_one : isZero Word256.one = Word256.zero := by
  unfold isZero Word256.zero Word256.one
  native_decide

theorem eq_refl (a : Word256) : eq a a = Word256.one := by
  unfold eq
  simp

theorem lt_irrefl (a : Word256) : lt a a = Word256.zero := by
  unfold lt
  simp

theorem gt_irrefl (a : Word256) : gt a a = Word256.zero := by
  unfold gt
  simp

/-- Addition overflow characterization: result wraps mod 2^256. -/
theorem add_toNat (a b : Word256) :
    (add a b).toNat = (a.toNat + b.toNat) % 2^256 := by
  unfold add
  exact BitVec.toNat_add a b

end LeanSP.Arith
