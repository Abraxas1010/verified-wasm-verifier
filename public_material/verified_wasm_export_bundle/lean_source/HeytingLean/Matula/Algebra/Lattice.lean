import Mathlib.Data.Nat.GCD.Basic
import HeytingLean.Matula.Algebra.Monoid

namespace HeytingLean
namespace Matula
namespace Algebra
namespace PosNat

/-- Divisibility preorder used for the Matula lattice framing. -/
def DvdLE (a b : PosNat) : Prop := a.1 ∣ b.1

infix:50 " ⪯ " => DvdLE

instance : LE PosNat := ⟨DvdLE⟩

@[simp] theorem dvdLE_def (a b : PosNat) : (a ⪯ b) ↔ a.1 ∣ b.1 := Iff.rfl
@[simp] theorem le_def (a b : PosNat) : (a ≤ b) ↔ a.1 ∣ b.1 := Iff.rfl

theorem dvdLE_refl (a : PosNat) : a ⪯ a := dvd_rfl

theorem dvdLE_trans {a b c : PosNat} (hab : a ⪯ b) (hbc : b ⪯ c) : a ⪯ c :=
  dvd_trans hab hbc

theorem dvdLE_antisymm {a b : PosNat} (hab : a ⪯ b) (hba : b ⪯ a) : a = b := by
  apply Subtype.ext
  exact Nat.dvd_antisymm hab hba

/-- Divisibility meet (greatest lower bound) via gcd. -/
def meet (a b : PosNat) : PosNat :=
  ⟨Nat.gcd a.1 b.1, Nat.gcd_pos_of_pos_left _ a.2⟩

/-- Divisibility join (least upper bound) via lcm. -/
def join (a b : PosNat) : PosNat :=
  ⟨Nat.lcm a.1 b.1, Nat.lcm_pos a.2 b.2⟩

@[simp] theorem meet_val (a b : PosNat) : (meet a b).1 = Nat.gcd a.1 b.1 := rfl
@[simp] theorem join_val (a b : PosNat) : (join a b).1 = Nat.lcm a.1 b.1 := rfl

theorem meet_le_left (a b : PosNat) : meet a b ⪯ a := by
  change Nat.gcd a.1 b.1 ∣ a.1
  exact Nat.gcd_dvd_left _ _

theorem meet_le_right (a b : PosNat) : meet a b ⪯ b := by
  change Nat.gcd a.1 b.1 ∣ b.1
  exact Nat.gcd_dvd_right _ _

theorem le_meet {a b c : PosNat} (hab : a ⪯ b) (hac : a ⪯ c) : a ⪯ meet b c := by
  change a.1 ∣ Nat.gcd b.1 c.1
  exact Nat.dvd_gcd hab hac

theorem le_join_left (a b : PosNat) : a ⪯ join a b := by
  change a.1 ∣ Nat.lcm a.1 b.1
  exact Nat.dvd_lcm_left _ _

theorem le_join_right (a b : PosNat) : b ⪯ join a b := by
  change b.1 ∣ Nat.lcm a.1 b.1
  exact Nat.dvd_lcm_right _ _

theorem join_le {a b c : PosNat} (hac : a ⪯ c) (hbc : b ⪯ c) : join a b ⪯ c := by
  change Nat.lcm a.1 b.1 ∣ c.1
  exact Nat.lcm_dvd hac hbc

instance : Preorder PosNat where
  le := (· ⪯ ·)
  lt := fun a b => a ⪯ b ∧ ¬ b ⪯ a
  le_refl := dvdLE_refl
  le_trans := @dvdLE_trans
  lt_iff_le_not_ge := by
    intro a b
    rfl

instance : PartialOrder PosNat where
  le_antisymm := @dvdLE_antisymm

instance : SemilatticeInf PosNat where
  inf := meet
  inf_le_left := meet_le_left
  inf_le_right := meet_le_right
  le_inf := by
    intro a b c hab hac
    exact le_meet hab hac

instance : SemilatticeSup PosNat where
  sup := join
  le_sup_left := le_join_left
  le_sup_right := le_join_right
  sup_le := by
    intro a b c hac hbc
    exact join_le hac hbc

instance : Lattice PosNat := {}

end PosNat

end Algebra
end Matula
end HeytingLean
