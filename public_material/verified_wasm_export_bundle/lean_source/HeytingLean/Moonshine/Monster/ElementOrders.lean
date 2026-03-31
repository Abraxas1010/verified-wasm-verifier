import HeytingLean.Moonshine.Monster.OrderFacts
import Mathlib.GroupTheory.Perm.Cycle.Type

set_option autoImplicit false

namespace HeytingLean.Moonshine

namespace MonsterOrder

/-!
Small, deterministic facts about which primes divide `monsterOrder`.

These feed directly into Cauchy's theorem (`exists_prime_orderOf_dvd_card`) for any `MonsterSpec`.
-/

lemma two_dvd : 2 ∣ monsterOrder := by
  dsimp [monsterOrder]
  have h0 : 2 ∣ (2 : Nat) ^ 46 := by
    exact dvd_pow (dvd_rfl) (by decide)
  have h1 : 2 ∣ (2 : Nat) ^ 46 * (3 : Nat) ^ 20 :=
    dvd_mul_of_dvd_left h0 ((3 : Nat) ^ 20)
  have h2 : 2 ∣ (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 :=
    dvd_mul_of_dvd_left h1 ((5 : Nat) ^ 9)
  have h3 : 2 ∣ (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 :=
    dvd_mul_of_dvd_left h2 ((7 : Nat) ^ 6)
  have h4 : 2 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 :=
    dvd_mul_of_dvd_left h3 ((11 : Nat) ^ 2)
  have h5 : 2 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 :=
    dvd_mul_of_dvd_left h4 ((13 : Nat) ^ 3)
  have h6 : 2 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 :=
    dvd_mul_of_dvd_left h5 17
  have h7 : 2 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 :=
    dvd_mul_of_dvd_left h6 19
  have h8 : 2 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 :=
    dvd_mul_of_dvd_left h7 23
  have h9 : 2 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 :=
    dvd_mul_of_dvd_left h8 29
  have h10 : 2 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 :=
    dvd_mul_of_dvd_left h9 31
  have h11 : 2 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 :=
    dvd_mul_of_dvd_left h10 41
  have h12 : 2 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 :=
    dvd_mul_of_dvd_left h11 47
  have h13 : 2 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 :=
    dvd_mul_of_dvd_left h12 59
  exact dvd_mul_of_dvd_left h13 71

lemma three_dvd : 3 ∣ monsterOrder := by
  dsimp [monsterOrder]
  have h0 : 3 ∣ (3 : Nat) ^ 20 := by
    exact dvd_pow (dvd_rfl) (by decide)
  have h1 : 3 ∣ (2 : Nat) ^ 46 * (3 : Nat) ^ 20 :=
    dvd_mul_of_dvd_right h0 ((2 : Nat) ^ 46)
  have h2 : 3 ∣ (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 :=
    dvd_mul_of_dvd_left h1 ((5 : Nat) ^ 9)
  have h3 : 3 ∣ (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 :=
    dvd_mul_of_dvd_left h2 ((7 : Nat) ^ 6)
  have h4 : 3 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 :=
    dvd_mul_of_dvd_left h3 ((11 : Nat) ^ 2)
  have h5 : 3 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 :=
    dvd_mul_of_dvd_left h4 ((13 : Nat) ^ 3)
  have h6 : 3 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 :=
    dvd_mul_of_dvd_left h5 17
  have h7 : 3 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 :=
    dvd_mul_of_dvd_left h6 19
  have h8 : 3 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 :=
    dvd_mul_of_dvd_left h7 23
  have h9 : 3 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 :=
    dvd_mul_of_dvd_left h8 29
  have h10 : 3 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 :=
    dvd_mul_of_dvd_left h9 31
  have h11 : 3 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 :=
    dvd_mul_of_dvd_left h10 41
  have h12 : 3 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 :=
    dvd_mul_of_dvd_left h11 47
  have h13 : 3 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 :=
    dvd_mul_of_dvd_left h12 59
  exact dvd_mul_of_dvd_left h13 71

lemma five_dvd : 5 ∣ monsterOrder := by
  dsimp [monsterOrder]
  have h0 : 5 ∣ (5 : Nat) ^ 9 := by
    exact dvd_pow (dvd_rfl) (by decide)
  have h1 : 5 ∣ (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 :=
    dvd_mul_of_dvd_right h0 ((2 : Nat) ^ 46 * (3 : Nat) ^ 20)
  have h2 : 5 ∣ (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 :=
    dvd_mul_of_dvd_left h1 ((7 : Nat) ^ 6)
  have h3 : 5 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 :=
    dvd_mul_of_dvd_left h2 ((11 : Nat) ^ 2)
  have h4 : 5 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 :=
    dvd_mul_of_dvd_left h3 ((13 : Nat) ^ 3)
  have h5 : 5 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 :=
    dvd_mul_of_dvd_left h4 17
  have h6 : 5 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 :=
    dvd_mul_of_dvd_left h5 19
  have h7 : 5 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 :=
    dvd_mul_of_dvd_left h6 23
  have h8 : 5 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 :=
    dvd_mul_of_dvd_left h7 29
  have h9 : 5 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 :=
    dvd_mul_of_dvd_left h8 31
  have h10 : 5 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 :=
    dvd_mul_of_dvd_left h9 41
  have h11 : 5 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 :=
    dvd_mul_of_dvd_left h10 47
  have h12 : 5 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 :=
    dvd_mul_of_dvd_left h11 59
  exact dvd_mul_of_dvd_left h12 71

lemma seven_dvd : 7 ∣ monsterOrder := by
  dsimp [monsterOrder]
  have h0 : 7 ∣ (7 : Nat) ^ 6 := by
    exact dvd_pow (dvd_rfl) (by decide)
  have h1 : 7 ∣ (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 :=
    dvd_mul_of_dvd_right h0 ((2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9)
  have h2 : 7 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 :=
    dvd_mul_of_dvd_left h1 ((11 : Nat) ^ 2)
  have h3 : 7 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 :=
    dvd_mul_of_dvd_left h2 ((13 : Nat) ^ 3)
  have h4 : 7 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 :=
    dvd_mul_of_dvd_left h3 17
  have h5 : 7 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 :=
    dvd_mul_of_dvd_left h4 19
  have h6 : 7 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 :=
    dvd_mul_of_dvd_left h5 23
  have h7 : 7 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 :=
    dvd_mul_of_dvd_left h6 29
  have h8 : 7 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 :=
    dvd_mul_of_dvd_left h7 31
  have h9 : 7 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 :=
    dvd_mul_of_dvd_left h8 41
  have h10 : 7 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 :=
    dvd_mul_of_dvd_left h9 47
  have h11 : 7 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 :=
    dvd_mul_of_dvd_left h10 59
  exact dvd_mul_of_dvd_left h11 71

lemma eleven_dvd : 11 ∣ monsterOrder := by
  dsimp [monsterOrder]
  have h0 : 11 ∣ (11 : Nat) ^ 2 := by
    exact dvd_pow (dvd_rfl) (by decide)
  have h1 : 11 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 :=
    dvd_mul_of_dvd_right h0 ((2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6)
  have h2 : 11 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 :=
    dvd_mul_of_dvd_left h1 ((13 : Nat) ^ 3)
  have h3 : 11 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 :=
    dvd_mul_of_dvd_left h2 17
  have h4 : 11 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 :=
    dvd_mul_of_dvd_left h3 19
  have h5 : 11 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 :=
    dvd_mul_of_dvd_left h4 23
  have h6 : 11 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 :=
    dvd_mul_of_dvd_left h5 29
  have h7 : 11 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 :=
    dvd_mul_of_dvd_left h6 31
  have h8 : 11 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 :=
    dvd_mul_of_dvd_left h7 41
  have h9 : 11 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 :=
    dvd_mul_of_dvd_left h8 47
  have h10 : 11 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 :=
    dvd_mul_of_dvd_left h9 59
  exact dvd_mul_of_dvd_left h10 71

lemma thirteen_dvd : 13 ∣ monsterOrder := by
  dsimp [monsterOrder]
  have h0 : 13 ∣ (13 : Nat) ^ 3 := by
    exact dvd_pow (dvd_rfl) (by decide)
  have h1 : 13 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 :=
    dvd_mul_of_dvd_right h0
      ((2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2)
  have h2 : 13 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 :=
    dvd_mul_of_dvd_left h1 17
  have h3 : 13 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 :=
    dvd_mul_of_dvd_left h2 19
  have h4 : 13 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 :=
    dvd_mul_of_dvd_left h3 23
  have h5 : 13 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 :=
    dvd_mul_of_dvd_left h4 29
  have h6 : 13 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 :=
    dvd_mul_of_dvd_left h5 31
  have h7 : 13 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 :=
    dvd_mul_of_dvd_left h6 41
  have h8 : 13 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 :=
    dvd_mul_of_dvd_left h7 47
  have h9 : 13 ∣
      (2 : Nat) ^ 46 * (3 : Nat) ^ 20 * (5 : Nat) ^ 9 * (7 : Nat) ^ 6 * (11 : Nat) ^ 2 *
        (13 : Nat) ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 :=
    dvd_mul_of_dvd_left h8 59
  exact dvd_mul_of_dvd_left h9 71

end MonsterOrder

namespace MonsterSpec

variable (S : MonsterSpec)

lemma exists_orderOf_eq_two : ∃ g : S.M, orderOf g = 2 := by
  classical
  have hdvd : 2 ∣ Fintype.card S.M := by
    simpa [S.card_eq] using MonsterOrder.two_dvd
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact exists_prime_orderOf_dvd_card 2 hdvd

lemma exists_orderOf_eq_three : ∃ g : S.M, orderOf g = 3 := by
  classical
  have hdvd : 3 ∣ Fintype.card S.M := by
    simpa [S.card_eq] using MonsterOrder.three_dvd
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact exists_prime_orderOf_dvd_card 3 hdvd

lemma exists_orderOf_eq_five : ∃ g : S.M, orderOf g = 5 := by
  classical
  have hdvd : 5 ∣ Fintype.card S.M := by
    simpa [S.card_eq] using MonsterOrder.five_dvd
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact exists_prime_orderOf_dvd_card 5 hdvd

lemma exists_orderOf_eq_seven : ∃ g : S.M, orderOf g = 7 := by
  classical
  have hdvd : 7 ∣ Fintype.card S.M := by
    simpa [S.card_eq] using MonsterOrder.seven_dvd
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact exists_prime_orderOf_dvd_card 7 hdvd

lemma exists_orderOf_eq_eleven : ∃ g : S.M, orderOf g = 11 := by
  classical
  have hdvd : 11 ∣ Fintype.card S.M := by
    simpa [S.card_eq] using MonsterOrder.eleven_dvd
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  exact exists_prime_orderOf_dvd_card 11 hdvd

lemma exists_orderOf_eq_thirteen : ∃ g : S.M, orderOf g = 13 := by
  classical
  have hdvd : 13 ∣ Fintype.card S.M := by
    simpa [S.card_eq] using MonsterOrder.thirteen_dvd
  haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
  exact exists_prime_orderOf_dvd_card 13 hdvd

end MonsterSpec

end HeytingLean.Moonshine
