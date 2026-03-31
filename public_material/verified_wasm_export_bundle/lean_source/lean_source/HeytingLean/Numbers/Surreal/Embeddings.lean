import HeytingLean.Numbers.Surreal.GameN
import HeytingLean.Numbers.Surreal.Operations
import HeytingLean.Numbers.Surreal.QuotOps

namespace HeytingLean
namespace Numbers
namespace Surreal

open HeytingLean.Numbers.SurrealCore

private def natToPreGame : Nat → PreGame
  | 0 => nullCut
  | Nat.succ n => PreGame.build [natToPreGame n] []

private noncomputable def intToPreGame : Int → PreGame
  | Int.ofNat n => natToPreGame n
  | Int.negSucc n => SurrealCore.neg (natToPreGame (Nat.succ n))

/-- Dyadic rationals `n / 2^k` as finite pre-games.

For odd numerators, use the canonical cut:
`n/2^(k+1) = {(n-1)/2^k | (n+1)/2^k}`.
-/
private noncomputable def dyadicToPreGame (n : Int) : Nat → PreGame
  | 0 => intToPreGame n
  | Nat.succ k =>
      if n % 2 = 0 then
        dyadicToPreGame (n / 2) k
      else
        let nL := (n - 1) / 2
        let nR := (n + 1) / 2
        PreGame.build [dyadicToPreGame nL k] [dyadicToPreGame nR k]

private def onePreGame : PreGame := PreGame.build [nullCut] []
/-- Reference pre-game cut for `1/2 = {0 | 1}`. -/
def oneHalfPreGame : PreGame := PreGame.build [nullCut] [onePreGame]

/-- Ordinal embedding into quotient surreals (finite prefix via naturals). -/
noncomputable def embedOrdinal (o : Nat) : SurrealQ :=
  Quotient.mk (s := approxSetoid) (canonicalize (natToPreGame o))

/-- Dyadic rationals as `num / 2^pow`. -/
structure Dyadic where
  num : Int
  pow : Nat

/-- Dyadic embedding into quotient surreals via denominator-sensitive pre-game recursion. -/
noncomputable def ofDyadic (d : Dyadic) : SurrealQ :=
  Quotient.mk (s := approxSetoid) (canonicalize (dyadicToPreGame d.num d.pow))

@[simp] theorem dyadicToPreGame_one_half :
    dyadicToPreGame (1 : Int) 1 = oneHalfPreGame := by
  simp [dyadicToPreGame, oneHalfPreGame, onePreGame, intToPreGame, natToPreGame]

@[simp] theorem dyadicToPreGame_double_succ (n : Int) (k : Nat) :
    dyadicToPreGame (2 * n) (Nat.succ k) = dyadicToPreGame n k := by
  simp [dyadicToPreGame]

theorem dyadicToPreGame_odd_succ (n : Int) (k : Nat) (hodd : n % 2 ≠ 0) :
    dyadicToPreGame n (Nat.succ k) =
      PreGame.build [dyadicToPreGame ((n - 1) / 2) k] [dyadicToPreGame ((n + 1) / 2) k] := by
  simp [dyadicToPreGame, hodd]

@[simp] theorem ofDyadic_one_half_ref :
    ofDyadic { num := Int.ofNat 1, pow := 1 } =
      Quotient.mk (s := approxSetoid) (canonicalize oneHalfPreGame) := by
  simp [ofDyadic, dyadicToPreGame_one_half]

@[simp] theorem ofDyadic_double_num_succ_pow (n : Int) (k : Nat) :
    ofDyadic { num := 2 * n, pow := Nat.succ k } = ofDyadic { num := n, pow := k } := by
  simp [ofDyadic]

@[simp] theorem ofDyadic_two_quarters_eq_one_half :
    ofDyadic { num := Int.ofNat 2, pow := 2 } =
      ofDyadic { num := Int.ofNat 1, pow := 1 } := by
  simp [ofDyadic, dyadicToPreGame]

@[simp] theorem ofDyadic_pow_zero_ofNat (n : Nat) :
    ofDyadic { num := Int.ofNat n, pow := 0 } = embedOrdinal n := rfl

end Surreal
end Numbers
end HeytingLean
