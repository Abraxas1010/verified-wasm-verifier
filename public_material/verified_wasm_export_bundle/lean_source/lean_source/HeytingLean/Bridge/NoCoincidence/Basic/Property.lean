import HeytingLean.Bridge.NoCoincidence.Basic.Circuit

namespace HeytingLean.Bridge.NoCoincidence.Basic

/-- "Ends in `n` zeros" means divisibility by `2^n`.
This is Neyman's zero-suffix condition from §2. -/
def endsInZeros (n : ℕ) (x : State n) : Prop :=
  x.1 % (2 ^ n) = 0

instance instDecidableEndsInZeros (n : ℕ) (x : State n) : Decidable (endsInZeros n x) := by
  unfold endsInZeros
  infer_instance

theorem endsInZeros_zero (n : ℕ) : endsInZeros n ⟨0, Nat.two_pow_pos _⟩ := by
  simp [endsInZeros]

private theorem two_dvd_two_pow (n : ℕ) (hn : 0 < n) : 2 ∣ 2 ^ n := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  refine ⟨2 ^ k, ?_⟩
  simpa [hk, Nat.mul_comm] using (Nat.pow_succ 2 k)

theorem endsInZeros_implies_even (n : ℕ) (hn : 0 < n) {x : State n}
    (hx : endsInZeros n x) : Even x.1 := by
  have hpow : 2 ^ n ∣ x.1 := Nat.dvd_of_mod_eq_zero hx
  have htwo : 2 ∣ 2 ^ n := two_dvd_two_pow n hn
  exact even_iff_two_dvd.2 (dvd_trans htwo hpow)

theorem not_endsInZeros_of_not_even (n : ℕ) (hn : 0 < n) {x : State n}
    (hx : ¬ Even x.1) : ¬ endsInZeros n x := by
  intro hZero
  exact hx (endsInZeros_implies_even n hn hZero)

/-- Neyman's property `P(C)`: every zero-suffix input is sent outside the zero-suffix region. -/
def PropertyP (n : ℕ) (C : RevCircuit n) : Prop :=
  ∀ x : State n, endsInZeros n x → ¬ endsInZeros n (C.eval x)

theorem identity_fails_P (n : ℕ) (_hn : 0 < n) : ¬ PropertyP n (RevCircuit.identity n) := by
  intro hP
  let x : State n := ⟨0, Nat.two_pow_pos _⟩
  have hZero : endsInZeros n x := endsInZeros_zero n
  exact hP x hZero hZero

theorem toggleLowBit_not_zeroSuffix (n : ℕ) (hn : 0 < n) (x : State n)
    (hx : endsInZeros n x) :
    ¬ endsInZeros n ((RevCircuit.lowBitToggleCircuit n hn).eval x) := by
  have hEven : Even x.1 := endsInZeros_implies_even n hn hx
  have hOddImage : ¬ Even (((RevCircuit.lowBitToggleCircuit n hn).eval x).1) := by
    change ¬ Even (x.1 ^^^ 1)
    rw [Nat.even_xor]
    simp [hEven]
  exact not_endsInZeros_of_not_even n hn hOddImage

theorem lowBitToggle_satisfies_P (n : ℕ) (hn : 0 < n) :
    PropertyP n (RevCircuit.lowBitToggleCircuit n hn) := by
  intro x hx
  exact toggleLowBit_not_zeroSuffix n hn x hx

end HeytingLean.Bridge.NoCoincidence.Basic
