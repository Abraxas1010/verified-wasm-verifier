import HeytingLean.Bridge.NoCoincidence.Basic.Property

namespace HeytingLean.Bridge.NoCoincidence.Basic

/-- Number of `3n`-bit states ending in `n` zeros. This is Neyman's `2^(2n)` count. -/
def zeroEndCount (n : ℕ) : ℕ :=
  2 ^ (2 * n)

/-- Total number of `3n`-bit states. -/
def stateCount (n : ℕ) : ℕ :=
  2 ^ (3 * n)

theorem zeroEndCount_sq (n : ℕ) :
    zeroEndCount n * zeroEndCount n = 2 ^ (4 * n) := by
  calc
    zeroEndCount n * zeroEndCount n
        = 2 ^ (2 * n) * 2 ^ (2 * n) := rfl
    _ = 2 ^ ((2 * n) + (2 * n)) := by rw [← Nat.pow_add]
    _ = 2 ^ (4 * n) := by congr; omega

/-- Neyman's counting heuristic: the expected collision mass is `2^n`. -/
theorem expectedCollisionMass (n : ℕ) :
    zeroEndCount n * zeroEndCount n = stateCount n * 2 ^ n := by
  calc
    zeroEndCount n * zeroEndCount n = 2 ^ (4 * n) := zeroEndCount_sq n
    _ = 2 ^ (3 * n + n) := by congr; omega
    _ = 2 ^ (3 * n) * 2 ^ n := by rw [Nat.pow_add]
    _ = stateCount n * 2 ^ n := rfl

/-- The exponential scale of the collision witness. This is the finite arithmetic core of the
`≈ e^{-2^n}` heuristic in Neyman's footnote 3. -/
theorem collision_mass_grows (n : ℕ) : 0 < 2 ^ n := by
  exact Nat.two_pow_pos n

end HeytingLean.Bridge.NoCoincidence.Basic
