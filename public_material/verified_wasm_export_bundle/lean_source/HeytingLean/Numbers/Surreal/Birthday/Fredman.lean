import HeytingLean.Numbers.Surreal.Birthday.Addition

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace Birthday

/-- Fredman's birthday multiplication recurrence on natural birthdays. -/
def fredman : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 0
  | n + 1, m + 1 => fredman n (m + 1) + fredman (n + 1) m + fredman n m + 1
termination_by n m => n + m

@[simp] theorem fredman_zero_left (m : Nat) : fredman 0 m = 0 := by
  cases m <;> simp [fredman]

@[simp] theorem fredman_zero_right (n : Nat) : fredman n 0 = 0 := by
  cases n <;> simp [fredman]

theorem fredman_symm : ∀ n m : Nat, fredman n m = fredman m n
  | 0, m => by
      cases m <;> simp
  | n + 1, 0 => by
      simp
  | n + 1, m + 1 => by
      rw [fredman, fredman]
      rw [fredman_symm n (m + 1), fredman_symm (n + 1) m, fredman_symm n m]
      simp [Nat.add_comm]

@[simp] theorem fredman_one_one : fredman 1 1 = 1 := by
  simp [fredman]

@[simp] theorem fredman_one_two : fredman 1 2 = 2 := by
  simp [fredman]

@[simp] theorem fredman_two_two : fredman 2 2 = 6 := by
  simp [fredman]

@[simp] theorem fredman_two_three : fredman 2 3 = 12 := by
  simp [fredman]

@[simp] theorem fredman_three_three : fredman 3 3 = 31 := by
  simp [fredman]

/-- Fredman is monotone in the first argument (one-step). -/
theorem fredman_le_succ_left : ∀ (a b : Nat),
    fredman a b ≤ fredman (a + 1) b
  | _, 0 => by simp
  | 0, b + 1 => by simp
  | a + 1, b + 1 => by
      show fredman (a + 1) (b + 1) ≤ fredman (a + 2) (b + 1)
      simp only [fredman]
      have h1 := fredman_le_succ_left a (b + 1)
      have h2 := fredman_le_succ_left (a + 1) b
      have h3 := fredman_le_succ_left a b
      omega

/-- Fredman is monotone in the first argument (general). -/
theorem fredman_mono_left {a₁ a₂ : Nat} (b : Nat) (h : a₁ ≤ a₂) :
    fredman a₁ b ≤ fredman a₂ b := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (fredman_le_succ_left _ b)

/-- Fredman is monotone in the second argument. -/
theorem fredman_mono_right (a : Nat) {b₁ b₂ : Nat} (h : b₁ ≤ b₂) :
    fredman a b₁ ≤ fredman a b₂ := by
  rw [fredman_symm a b₁, fredman_symm a b₂]
  exact fredman_mono_left a h

/-- Fredman is monotone in both arguments. -/
theorem fredman_mono {a₁ a₂ b₁ b₂ : Nat} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    fredman a₁ b₁ ≤ fredman a₂ b₂ :=
  le_trans (fredman_mono_left b₁ ha) (fredman_mono_right a₂ hb)

/-- Fredman is strictly positive for positive inputs. -/
theorem fredman_pos {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    0 < fredman m n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hm)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  simp [fredman]

end Birthday
end Surreal
end Numbers
end HeytingLean
