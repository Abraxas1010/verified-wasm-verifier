import HeytingLean.Numbers.Surreal.Birthday.Core
import HeytingLean.Numbers.Surreal.LoFProgram

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace Birthday

@[simp] theorem nullCut_birth :
    SurrealCore.nullCut.birth = 0 := rfl

@[simp] theorem natPreGame_birth : ∀ n : Nat,
    (LoFProgram.natPreGame n).birth = n
  | 0 => by
      simp [LoFProgram.natPreGame, SurrealCore.nullCut]
  | Nat.succ n => by
      simp [LoFProgram.natPreGame, natPreGame_birth n, SurrealCore.PreGame.build,
        SurrealCore.PreGame.maxBirth]

@[simp] theorem normalize_natPreGame : ∀ n : Nat,
    normalize (LoFProgram.natPreGame n) = LoFProgram.natPreGame n
  | 0 => by
      simp [LoFProgram.natPreGame, normalize_nullCut]
  | Nat.succ n => by
      simp [LoFProgram.natPreGame, normalize_natPreGame n]

@[simp] theorem normalizedBirthday_natPreGame : ∀ n : Nat,
    normalizedBirthday (LoFProgram.natPreGame n) = n
  | 0 => by
      simp [normalizedBirthday, SurrealCore.birthday, LoFProgram.natPreGame, normalize_nullCut]
  | Nat.succ n => by
      simp [normalizedBirthday, LoFProgram.natPreGame, normalize_natPreGame]

@[simp] theorem negNatPreGame_birth : ∀ n : Nat,
    (LoFProgram.negNatPreGame n).birth = n + 1
  | 0 => by
      simp [LoFProgram.negNatPreGame, SurrealCore.PreGame.build, SurrealCore.PreGame.maxBirth,
        SurrealCore.nullCut]
  | Nat.succ n => by
      simp [LoFProgram.negNatPreGame, negNatPreGame_birth n, SurrealCore.PreGame.build,
        SurrealCore.PreGame.maxBirth, Nat.add_assoc]

@[simp] theorem normalize_negNatPreGame : ∀ n : Nat,
    normalize (LoFProgram.negNatPreGame n) = LoFProgram.negNatPreGame n
  | 0 => by
      simp [LoFProgram.negNatPreGame, normalize_nullCut]
  | Nat.succ n => by
      simp [LoFProgram.negNatPreGame, normalize_negNatPreGame n]

@[simp] theorem normalizedBirthday_negNatPreGame : ∀ n : Nat,
    normalizedBirthday (LoFProgram.negNatPreGame n) = n + 1
  | 0 => by
      rw [normalizedBirthday, normalize_negNatPreGame 0, SurrealCore.birthday]
      exact negNatPreGame_birth 0
  | Nat.succ n => by
      simp [normalizedBirthday, LoFProgram.negNatPreGame, normalize_negNatPreGame]

@[simp] theorem normalizedBirthday_intPreGame (z : Int) :
    normalizedBirthday (LoFProgram.intPreGame z) = Int.natAbs z := by
  cases z using Int.rec <;> simp [LoFProgram.intPreGame]

theorem normalizedBirthday_build_single_pair (l r : BirthdayForm) :
    normalizedBirthday (SurrealCore.PreGame.build [l] [r]) =
      Nat.succ (Nat.max (normalizedBirthday l) (normalizedBirthday r)) := by
  rw [normalizedBirthday_eq, normalize_build_left_cons, normalizedBirthday_eq]
  change Nat.succ
      (Nat.max (SurrealCore.PreGame.maxBirth [normalize l]) (SurrealCore.PreGame.maxBirth [normalize r])) =
    Nat.succ (Nat.max (normalize l).birth (normalize r).birth)
  simp [SurrealCore.PreGame.maxBirth]

theorem normalizedBirthday_dyadicPreGame_succ_even (n : Int) (k : Nat) (h : n % 2 = 0) :
    normalizedBirthday (LoFProgram.dyadicPreGame n (k + 1)) =
      normalizedBirthday (LoFProgram.dyadicPreGame (n / 2) k) := by
  simp [LoFProgram.dyadicPreGame, h]

theorem normalizedBirthday_dyadicPreGame_succ_odd (n : Int) (k : Nat) (h : n % 2 ≠ 0) :
    normalizedBirthday (LoFProgram.dyadicPreGame n (k + 1)) =
      Nat.succ
        (Nat.max
          (normalizedBirthday (LoFProgram.dyadicPreGame ((n - 1) / 2) k))
          (normalizedBirthday (LoFProgram.dyadicPreGame ((n + 1) / 2) k))) := by
  rw [LoFProgram.dyadicPreGame, if_neg h, normalizedBirthday_build_single_pair]

@[simp] theorem normalizedBirthday_oneHalf :
    normalizedBirthday (LoFProgram.dyadicPreGame 1 1) = 2 := by
  rw [normalizedBirthday_dyadicPreGame_succ_odd (n := 1) (k := 0) (by decide)]
  have hL : (((1 : Int) - 1) / 2) = 0 := by native_decide
  have hR : (((1 : Int) + 1) / 2) = 1 := by native_decide
  rw [hL, hR]
  have h0 : normalizedBirthday (LoFProgram.dyadicPreGame 0 0) = 0 := by
    simpa [LoFProgram.dyadicPreGame] using normalizedBirthday_intPreGame (0 : Int)
  have h1 : normalizedBirthday (LoFProgram.dyadicPreGame 1 0) = 1 := by
    simpa [LoFProgram.dyadicPreGame] using normalizedBirthday_intPreGame (1 : Int)
  rw [h0, h1]
  decide

@[simp] theorem normalizedBirthday_threeHalves :
    normalizedBirthday (LoFProgram.dyadicPreGame 3 1) = 3 := by
  rw [normalizedBirthday_dyadicPreGame_succ_odd (n := 3) (k := 0) (by decide)]
  have hL : (((3 : Int) - 1) / 2) = 1 := by native_decide
  have hR : (((3 : Int) + 1) / 2) = 2 := by native_decide
  rw [hL, hR]
  have h1 : normalizedBirthday (LoFProgram.dyadicPreGame 1 0) = 1 := by
    simpa [LoFProgram.dyadicPreGame] using normalizedBirthday_intPreGame (1 : Int)
  have h2 : normalizedBirthday (LoFProgram.dyadicPreGame 2 0) = 2 := by
    simpa [LoFProgram.dyadicPreGame] using normalizedBirthday_intPreGame (2 : Int)
  rw [h1, h2]
  decide

@[simp] theorem normalizedBirthday_oneQuarter :
    normalizedBirthday (LoFProgram.dyadicPreGame 1 2) = 3 := by
  rw [normalizedBirthday_dyadicPreGame_succ_odd (n := 1) (k := 1) (by decide)]
  have hL : (((1 : Int) - 1) / 2) = 0 := by native_decide
  have hR : (((1 : Int) + 1) / 2) = 1 := by native_decide
  rw [hL, hR]
  rw [normalizedBirthday_dyadicPreGame_succ_even (n := 0) (k := 0) (by decide)]
  have hZ : ((0 : Int) / 2) = 0 := by native_decide
  rw [hZ]
  have h0 : normalizedBirthday (LoFProgram.dyadicPreGame 0 0) = 0 := by
    simpa [LoFProgram.dyadicPreGame] using normalizedBirthday_intPreGame (0 : Int)
  rw [h0, normalizedBirthday_oneHalf]
  decide

@[simp] theorem normalizedBirthday_minusOneHalf :
    normalizedBirthday (LoFProgram.dyadicPreGame (-1) 1) = 2 := by
  rw [normalizedBirthday_dyadicPreGame_succ_odd (n := -1) (k := 0) (by decide)]
  have hL : (((-1 : Int) - 1) / 2) = -1 := by native_decide
  have hR : (((-1 : Int) + 1) / 2) = 0 := by native_decide
  rw [hL, hR]
  have hNeg1 : normalizedBirthday (LoFProgram.dyadicPreGame (-1) 0) = 1 := by
    simpa [LoFProgram.dyadicPreGame] using normalizedBirthday_intPreGame (-1 : Int)
  have h0 : normalizedBirthday (LoFProgram.dyadicPreGame 0 0) = 0 := by
    simpa [LoFProgram.dyadicPreGame] using normalizedBirthday_intPreGame (0 : Int)
  rw [hNeg1, h0]
  decide

@[simp] theorem normalizedBirthday_twoQuarters :
    normalizedBirthday (LoFProgram.dyadicPreGame 2 2) = 2 := by
  rw [normalizedBirthday_dyadicPreGame_succ_even (n := 2) (k := 1) (by decide)]
  exact normalizedBirthday_oneHalf

@[simp] theorem normalizedBirthday_minusThreeHalves :
    normalizedBirthday (LoFProgram.dyadicPreGame (-3) 1) = 3 := by
  rw [normalizedBirthday_dyadicPreGame_succ_odd (n := -3) (k := 0) (by decide)]
  have hL : (((-3 : Int) - 1) / 2) = -2 := by native_decide
  have hR : (((-3 : Int) + 1) / 2) = -1 := by native_decide
  rw [hL, hR]
  have hNeg2 : normalizedBirthday (LoFProgram.dyadicPreGame (-2) 0) = 2 := by
    simpa [LoFProgram.dyadicPreGame] using normalizedBirthday_intPreGame (-2 : Int)
  have hNeg1 : normalizedBirthday (LoFProgram.dyadicPreGame (-1) 0) = 1 := by
    simpa [LoFProgram.dyadicPreGame] using normalizedBirthday_intPreGame (-1 : Int)
  rw [hNeg2, hNeg1]
  decide

end Birthday
end Surreal
end Numbers
end HeytingLean
