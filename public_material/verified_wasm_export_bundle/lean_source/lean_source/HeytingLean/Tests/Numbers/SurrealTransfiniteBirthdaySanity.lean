import HeytingLean.Numbers.Ordinal.Notation
import HeytingLean.Numbers.Surreal.TransfinitePreGame

/-!
# Sanity checks: transfinite birthdays (toy model)

These are executable (decidable) checks that our compact option-set model assigns the
expected ordinal birthdays to the canonical examples:
- naturals: finite birthdays
- ω: limit birthday via `{0,1,2,... | }`
- ω+n and ω+ω via compact infinite families
-/

namespace HeytingLean.Tests.Numbers.SurrealTransfiniteBirthdaySanity

open HeytingLean.Numbers.Ordinal
open HeytingLean.Numbers.Surreal.TransfinitePreGame

example : birth PreGame.zero = 0 := by
  native_decide

example : birth (PreGame.nat 7) = OrdinalCNF.ofNat 7 := by
  native_decide

example : birth PreGame.omega = OrdinalCNF.omega := by
  native_decide

example : birth (PreGame.nat 0) = (0 : OrdinalCNF) := by
  simp [birth_nat_zero]

example (n : Nat) :
    birth (PreGame.nat (Nat.succ n)) =
      OrdinalCNF.succ (birth (PreGame.nat n)) := by
  simp [birth_nat_succ]

example : birth PreGame.omega = OrdinalCNF.omega := by
  simp [birth_omega]

example :
    birth PreGame.omegaTimesTwo = OrdinalCNF.omega + OrdinalCNF.omega := by
  simp [birth_omegaTimesTwo]

example :
    birth PreGame.omegaTimesThree = OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.omega := by
  simp [birth_omegaTimesThree]

example (n : Nat) :
    birth (PreGame.omegaPlusNat (Nat.succ n)) =
      OrdinalCNF.max OrdinalCNF.omega
        (OrdinalCNF.supList
          ((PreGame.omegaPlusNatList (Nat.succ n)).map
            (fun g => OrdinalCNF.succ (birth g)))) := by
  exact birth_omegaPlusNat_succ_unfold n

example (n : Nat) :
    birth (PreGame.omegaTimesTwoPlusNat (Nat.succ n)) =
      OrdinalCNF.max OrdinalCNF.omega
        (OrdinalCNF.max (OrdinalCNF.omega + OrdinalCNF.omega)
          (OrdinalCNF.supList
            ((PreGame.omegaTimesTwoPlusNatList (Nat.succ n)).map
              (fun g => OrdinalCNF.succ (birth g))))) := by
  exact birth_omegaTimesTwoPlusNat_succ_unfold n

example (n : Nat) :
    OrdinalCNF.omega ≤ birth (PreGame.omegaPlusNat n) := by
  exact birth_omegaPlusNat_ge_omega n

example (n : Nat) :
    OrdinalCNF.omega + OrdinalCNF.omega ≤ birth (PreGame.omegaTimesTwoPlusNat n) := by
  exact birth_omegaTimesTwoPlusNat_ge_omegaTimesTwo n

example :
    birth (PreGame.omegaPlusNat 1) =
      OrdinalCNF.omega + OrdinalCNF.ofNat 1 := by
  native_decide

example :
    birth (PreGame.omegaPlusNat 2) =
      OrdinalCNF.omega + OrdinalCNF.ofNat 2 := by
  simp [birth_omegaPlusNat_two]

example :
    birth (PreGame.omegaPlusNat 3) =
      OrdinalCNF.omega + OrdinalCNF.ofNat 3 := by
  simp [birth_omegaPlusNat_three]

example :
    birth (PreGame.omegaTimesTwoPlusNat 1) =
      OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat 1 := by
  native_decide

example :
    birth (PreGame.omegaTimesTwoPlusNat 2) =
      OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat 2 := by
  simp [birth_omegaTimesTwoPlusNat_two]

example :
    birth (PreGame.omegaTimesTwoPlusNat 3) =
      OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.ofNat 3 := by
  simp [birth_omegaTimesTwoPlusNat_three]

example :
    supSucc OptionSet.omegaPlusNats =
      OrdinalCNF.omega + OrdinalCNF.omega := by
  native_decide

example :
    birth (.cut .omegaPlusNats (.finite [])) =
      OrdinalCNF.omega + OrdinalCNF.omega := by
  native_decide

example :
    supSucc OptionSet.omegaTimesTwoPlusNats =
      OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.omega := by
  native_decide

example :
    birth (.cut .omegaTimesTwoPlusNats (.finite [])) =
      OrdinalCNF.omega + OrdinalCNF.omega + OrdinalCNF.omega := by
  native_decide

example (fuel : Nat) (g : PreGame) :
    (CoreApprox.toCore fuel g).birth ≤ fuel := by
  exact CoreApprox.toCore_birth_le fuel g

example :
    CoreApprox.toCore 0 PreGame.omega = HeytingLean.Numbers.SurrealCore.nullCut := by
  exact CoreApprox.toCore_zeroFuel PreGame.omega

example :
    CoreApprox.toCore 4 PreGame.zero = HeytingLean.Numbers.SurrealCore.nullCut := by
  simp [CoreApprox.toCore_succ_zero]

example :
    (CoreApprox.toCore 4 PreGame.zero).birth = 0 := by
  simp [CoreApprox.toCore_succ_zero, HeytingLean.Numbers.SurrealCore.nullCut]

example :
    (CoreApprox.toCore 3 PreGame.zero).birth ≤ 3 := by
  exact CoreApprox.toCore_birth_le 3 PreGame.zero

example :
    (CoreApprox.toCore 4 PreGame.omega).birth ≤ 4 := by
  exact CoreApprox.toCore_birth_le 4 PreGame.omega

example (fuel : Nat) :
    0 < (CoreApprox.toCore (Nat.succ (Nat.succ fuel)) PreGame.omega).birth := by
  exact CoreApprox.toCore_succ_succ_omega_birth_pos fuel

example (fuel : Nat) :
    1 ≤ (CoreApprox.toCore (Nat.succ (Nat.succ fuel)) PreGame.omega).birth ∧
      (CoreApprox.toCore (Nat.succ (Nat.succ fuel)) PreGame.omega).birth ≤ Nat.succ (Nat.succ fuel) := by
  exact CoreApprox.toCore_succ_succ_omega_birth_bounds fuel

example :
    (CoreApprox.toCore 1 PreGame.omega).birth = 0 := by
  native_decide

example :
    (CoreApprox.toCore 2 PreGame.omega).birth = 1 := by
  native_decide

example :
    (CoreApprox.toCore 3 PreGame.omega).birth = 1 := by
  native_decide

example :
    (CoreApprox.toCore 4 PreGame.omega).birth = 2 := by
  native_decide

example :
    (CoreApprox.toCore 5 (PreGame.omegaPlusNat 2)).birth ≤ 5 := by
  exact CoreApprox.toCore_birth_le 5 (PreGame.omegaPlusNat 2)

example :
    (CoreApprox.toCore 5 PreGame.omegaTimesThree).birth ≤ 5 := by
  exact CoreApprox.toCore_birth_le 5 PreGame.omegaTimesThree

example (fuel n : Nat) :
    0 < (CoreApprox.toCore (Nat.succ (Nat.succ fuel)) (PreGame.omegaPlusNat n)).birth := by
  exact CoreApprox.toCore_succ_succ_omegaPlusNat_birth_pos fuel n

example (fuel n : Nat) :
    1 ≤ (CoreApprox.toCore (Nat.succ (Nat.succ fuel)) (PreGame.omegaPlusNat n)).birth ∧
      (CoreApprox.toCore (Nat.succ (Nat.succ fuel)) (PreGame.omegaPlusNat n)).birth ≤ Nat.succ (Nat.succ fuel) := by
  exact CoreApprox.toCore_succ_succ_omegaPlusNat_birth_bounds fuel n

example (fuel : Nat) :
    0 < (CoreApprox.toCore (Nat.succ (Nat.succ fuel)) PreGame.omegaTimesTwo).birth := by
  exact CoreApprox.toCore_succ_succ_omegaTimesTwo_birth_pos fuel

example (fuel : Nat) :
    1 ≤ (CoreApprox.toCore (Nat.succ (Nat.succ fuel)) PreGame.omegaTimesTwo).birth ∧
      (CoreApprox.toCore (Nat.succ (Nat.succ fuel)) PreGame.omegaTimesTwo).birth ≤ Nat.succ (Nat.succ fuel) := by
  exact CoreApprox.toCore_succ_succ_omegaTimesTwo_birth_bounds fuel

example (fuel : Nat) :
    0 < (CoreApprox.toCore (Nat.succ (Nat.succ fuel)) PreGame.omegaTimesThree).birth := by
  exact CoreApprox.toCore_succ_succ_omegaTimesThree_birth_pos fuel

example (fuel : Nat) :
    1 ≤ (CoreApprox.toCore (Nat.succ (Nat.succ fuel)) PreGame.omegaTimesThree).birth ∧
      (CoreApprox.toCore (Nat.succ (Nat.succ fuel)) PreGame.omegaTimesThree).birth ≤ Nat.succ (Nat.succ fuel) := by
  exact CoreApprox.toCore_succ_succ_omegaTimesThree_birth_bounds fuel

example :
    (CoreApprox.toCore 2 (PreGame.omegaPlusNat 1)).birth = 1 := by
  native_decide

example :
    (CoreApprox.toCore 3 (PreGame.omegaPlusNat 1)).birth = 1 := by
  native_decide

example :
    (CoreApprox.toCore 4 (PreGame.omegaPlusNat 2)).birth ≤ 4 := by
  native_decide

example :
    (CoreApprox.toCore 14 (PreGame.nat 7)).birth = 7 := by
  native_decide

example (n fuel : Nat) :
    (CoreApprox.toCore fuel (PreGame.nat n)).birth = Nat.min n (fuel / 2) := by
  exact CoreApprox.toCore_nat_birth_eq_min_half_fuel n fuel

example (n fuel : Nat) :
    (CoreApprox.toCore fuel (PreGame.nat n)).birth ≤
      (CoreApprox.toCore (Nat.succ fuel) (PreGame.nat n)).birth := by
  exact CoreApprox.toCore_nat_birth_mono_fuel n fuel

example (fuel : Nat) :
    (CoreApprox.toCore fuel PreGame.omega).birth = fuel / 2 := by
  exact CoreApprox.toCore_omega_birth_eq_half_fuel fuel

example (fuel n : Nat) :
    (CoreApprox.toCore fuel (PreGame.omegaPlusNat n)).birth = fuel / 2 := by
  exact CoreApprox.toCore_omegaPlusNat_birth_eq_half_fuel fuel n

example (fuel n : Nat) :
    (CoreApprox.toCore fuel (PreGame.omegaTimesTwoPlusNat n)).birth = fuel / 2 := by
  exact CoreApprox.toCore_omegaTimesTwoPlusNat_birth_eq_half_fuel fuel n

example (fuel : Nat) :
    (CoreApprox.toCore fuel PreGame.omegaTimesThree).birth = fuel / 2 := by
  exact CoreApprox.toCore_omegaTimesThree_birth_eq_half_fuel fuel

example (fuel : Nat) :
    (CoreApprox.toCore fuel PreGame.omega).birth ≤
      (CoreApprox.toCore (Nat.succ fuel) PreGame.omega).birth := by
  exact CoreApprox.toCore_omega_birth_mono_fuel fuel

example (fuel n : Nat) :
    (CoreApprox.toCore fuel (PreGame.omegaPlusNat n)).birth ≤
      (CoreApprox.toCore (Nat.succ fuel) (PreGame.omegaPlusNat n)).birth := by
  exact CoreApprox.toCore_omegaPlusNat_birth_mono_fuel fuel n

example (fuel : Nat) :
    (CoreApprox.toCore fuel PreGame.omegaTimesTwo).birth ≤
      (CoreApprox.toCore (Nat.succ fuel) PreGame.omegaTimesTwo).birth := by
  exact CoreApprox.toCore_omegaTimesTwo_birth_mono_fuel fuel

example (fuel n : Nat) :
    (CoreApprox.toCore fuel (PreGame.omegaTimesTwoPlusNat n)).birth ≤
      (CoreApprox.toCore (Nat.succ fuel) (PreGame.omegaTimesTwoPlusNat n)).birth := by
  exact CoreApprox.toCore_omegaTimesTwoPlusNat_birth_mono_fuel fuel n

example (fuel : Nat) :
    (CoreApprox.toCore fuel PreGame.omegaTimesThree).birth ≤
      (CoreApprox.toCore (Nat.succ fuel) PreGame.omegaTimesThree).birth := by
  exact CoreApprox.toCore_omegaTimesThree_birth_mono_fuel fuel

example (fuel n : Nat) :
    (CoreApprox.toCore fuel (PreGame.omegaPlusNat n)).birth =
      (CoreApprox.toCore fuel PreGame.omega).birth := by
  exact CoreApprox.toCore_omegaPlusNat_birth_eq_omega_birth fuel n

example (fuel : Nat) :
    (CoreApprox.toCore fuel PreGame.omegaTimesTwo).birth = fuel / 2 := by
  exact CoreApprox.toCore_omegaTimesTwo_birth_eq_half_fuel fuel

example (fuel : Nat) :
    (CoreApprox.toCore fuel PreGame.omegaTimesTwo).birth =
      (CoreApprox.toCore fuel PreGame.omega).birth := by
  exact CoreApprox.toCore_omegaTimesTwo_birth_eq_omega_birth fuel

example (fuel n : Nat) :
    (CoreApprox.toCore fuel (PreGame.omegaTimesTwoPlusNat n)).birth =
      (CoreApprox.toCore fuel PreGame.omega).birth := by
  exact CoreApprox.toCore_omegaTimesTwoPlusNat_birth_eq_omega_birth fuel n

example (fuel : Nat) :
    (CoreApprox.toCore fuel PreGame.omegaTimesThree).birth =
      (CoreApprox.toCore fuel PreGame.omega).birth := by
  exact CoreApprox.toCore_omegaTimesThree_birth_eq_omega_birth fuel

example :
    (CoreApprox.toCore 2 PreGame.omegaTimesThree).birth = 1 := by
  native_decide

example :
    (CoreApprox.toCore 4 PreGame.omegaTimesThree).birth = 2 := by
  native_decide

example :
    (CoreApprox.toCore 2 (PreGame.nat 1)).birth = 1 := by
  native_decide

example :
    (CoreApprox.toCore 4 (PreGame.nat 2)).birth = 2 := by
  native_decide

example :
    (CoreApprox.toCore 6 (PreGame.nat 3)).birth = 3 := by
  native_decide

end HeytingLean.Tests.Numbers.SurrealTransfiniteBirthdaySanity
