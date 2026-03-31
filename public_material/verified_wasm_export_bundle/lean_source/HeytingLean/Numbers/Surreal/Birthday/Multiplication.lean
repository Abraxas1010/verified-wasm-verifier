import HeytingLean.Numbers.Surreal.Birthday.Fredman

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace Birthday

open HeytingLean.Numbers.SurrealCore

private abbrev MulRel :=
  @WellFoundedRelation.rel (PreGame × PreGame)
    (measure (fun p : PreGame × PreGame => sizeOf p.1 + sizeOf p.2))

private abbrev MulBodyTy :=
  (p : PreGame × PreGame) →
    ((q : PreGame × PreGame) → MulRel q p → PreGame) →
    PreGame

private def listBindMul {α β : Type} (xs : List α) (f : α → List β) : List β :=
  xs.foldr (fun x acc => f x ++ acc) []

private noncomputable def subMul (x y : PreGame) : PreGame :=
  SurrealCore.add x (SurrealCore.neg y)

private noncomputable def mulBodyExplicit : MulBodyTy :=
  fun p ih =>
    let x := p.fst
    let y := p.snd
    let L₁ :=
      listBindMul x.L.attach (fun xl =>
        y.L.attach.map (fun (yl : { g // g ∈ y.L }) =>
          subMul
            (SurrealCore.add (ih (↑xl, y) (SurrealCore.mul._proof_4 p xl))
              (ih (x, ↑yl) (SurrealCore.mul._proof_5 p yl)))
            (ih (↑xl, ↑yl) (SurrealCore.mul._proof_7 p xl yl))))
    let L₂ :=
      listBindMul x.R.attach (fun xr =>
        y.R.attach.map (fun (yr : { g // g ∈ y.R }) =>
          subMul
            (SurrealCore.add (ih (↑xr, y) (SurrealCore.mul._proof_10 p xr))
              (ih (x, ↑yr) (SurrealCore.mul._proof_11 p yr)))
            (ih (↑xr, ↑yr) (SurrealCore.mul._proof_13 p xr yr))))
    let R₁ :=
      listBindMul x.L.attach (fun xl =>
        y.R.attach.map (fun (yr : { g // g ∈ y.R }) =>
          subMul
            (SurrealCore.add (ih (↑xl, y) (SurrealCore.mul._proof_4 p xl))
              (ih (x, ↑yr) (SurrealCore.mul._proof_11 p yr)))
            (ih (↑xl, ↑yr) (SurrealCore.mul._proof_15 p xl yr))))
    let R₂ :=
      listBindMul x.R.attach (fun xr =>
        y.L.attach.map (fun (yl : { g // g ∈ y.L }) =>
          subMul
            (SurrealCore.add (ih (↑xr, y) (SurrealCore.mul._proof_10 p xr))
              (ih (x, ↑yl) (SurrealCore.mul._proof_5 p yl)))
            (ih (↑xr, ↑yl) (SurrealCore.mul._proof_17 p xr yl))))
    PreGame.build (L₁ ++ L₂) (R₁ ++ R₂)

private theorem mul_eq_explicit :
    SurrealCore.mul =
      fun x y : PreGame =>
        if isNullCut x || isNullCut y then nullCut
        else (SurrealCore.mul._proof_1.fix mulBodyExplicit (x, y) : PreGame) := by
  simpa [mulBodyExplicit] using SurrealCore.mul.eq_1

private noncomputable def coreMul (x y : PreGame) : PreGame :=
  (SurrealCore.mul._proof_1.fix mulBodyExplicit (x, y) : PreGame)

private theorem coreMul_nullCut_left (y : PreGame) :
    coreMul SurrealCore.nullCut y = SurrealCore.PreGame.build [] [] := by
  unfold coreMul
  rw [WellFounded.fix_eq (hwf := SurrealCore.mul._proof_1) (F := mulBodyExplicit)
    (x := (SurrealCore.nullCut, y))]
  simp [mulBodyExplicit, listBindMul, subMul, SurrealCore.nullCut, PreGame.build]

private theorem coreMul_nullCut_right (x : PreGame) :
    coreMul x SurrealCore.nullCut = SurrealCore.PreGame.build [] [] := by
  unfold coreMul
  rw [WellFounded.fix_eq (hwf := SurrealCore.mul._proof_1) (F := mulBodyExplicit)
    (x := (x, SurrealCore.nullCut))]
  simp [mulBodyExplicit, listBindMul, subMul, SurrealCore.nullCut, PreGame.build]

@[simp] private theorem normalizedBirthday_coreMul_nullCut_left (y : PreGame) :
    normalizedBirthday (coreMul SurrealCore.nullCut y) = 0 := by
  rw [coreMul_nullCut_left]
  simp [normalizedBirthday, normalize, LoFProgram.normalize.eq_def, PreGame.build,
    SurrealCore.nullCut, SurrealCore.birthday]

@[simp] private theorem normalizedBirthday_coreMul_nullCut_right (x : PreGame) :
    normalizedBirthday (coreMul x SurrealCore.nullCut) = 0 := by
  rw [coreMul_nullCut_right]
  simp [normalizedBirthday, normalize, LoFProgram.normalize.eq_def, PreGame.build,
    SurrealCore.nullCut, SurrealCore.birthday]

@[simp] theorem birthdayMul_nullCut_left (x : BirthdayForm) :
    birthdayMul SurrealCore.nullCut x = SurrealCore.nullCut := by
  simp [birthdayMul, normalize_nullCut, SurrealCore.mul_nullCut_left]

@[simp] theorem birthdayMul_nullCut_right (x : BirthdayForm) :
    birthdayMul x SurrealCore.nullCut = SurrealCore.nullCut := by
  simp [birthdayMul, normalize_nullCut, SurrealCore.mul_nullCut_right]

@[simp] theorem birthdayMul_nullCut_left_birth (x : BirthdayForm) :
    (birthdayMul SurrealCore.nullCut x).birth = 0 := by
  simp

@[simp] theorem birthdayMul_nullCut_right_birth (x : BirthdayForm) :
    (birthdayMul x SurrealCore.nullCut).birth = 0 := by
  simp

/-- Exact Fredman agreement on the zero boundary of the multiplication lane. -/
@[simp] theorem birthdayMul_natPreGame_zero_left (n : Nat) :
    (birthdayMul (LoFProgram.natPreGame 0) (LoFProgram.natPreGame n)).birth = fredman 0 n := by
  simp [LoFProgram.natPreGame]

/-- Exact Fredman agreement on the zero boundary of the multiplication lane. -/
@[simp] theorem birthdayMul_natPreGame_zero_right (n : Nat) :
    (birthdayMul (LoFProgram.natPreGame n) (LoFProgram.natPreGame 0)).birth = fredman n 0 := by
  simp [LoFProgram.natPreGame]

private theorem normalizedBirthday_coreMul_natPreGame_eq_birthdayMul : ∀ m n : Nat,
    normalizedBirthday (coreMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame n)) =
      (birthdayMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame n)).birth
  | 0, n => by
      simpa [LoFProgram.natPreGame, coreMul, birthdayMul, mul_eq_explicit] using
        normalizedBirthday_coreMul_nullCut_left (LoFProgram.natPreGame n)
  | m + 1, 0 => by
      simpa [LoFProgram.natPreGame, coreMul, birthdayMul, mul_eq_explicit] using
        normalizedBirthday_coreMul_nullCut_right (LoFProgram.natPreGame (m + 1))
  | m + 1, n + 1 => by
      have hm :
          LoFProgram.natPreGame (m + 1) =
            ({ L := [LoFProgram.natPreGame m], R := [], birth := m + 1 } : PreGame) := by
        simp [LoFProgram.natPreGame, PreGame.build, PreGame.maxBirth, natPreGame_birth]
      have hn :
          LoFProgram.natPreGame (n + 1) =
            ({ L := [LoFProgram.natPreGame n], R := [], birth := n + 1 } : PreGame) := by
        simp [LoFProgram.natPreGame, PreGame.build, PreGame.maxBirth, natPreGame_birth]
      rw [hm, hn]
      simp [birthdayMul, coreMul, mul_eq_explicit, SurrealCore.isNullCut]

private theorem birthdayMul_natPreGame_succ_succ_birth (m n : Nat) :
    (birthdayMul (LoFProgram.natPreGame (m + 1)) (LoFProgram.natPreGame (n + 1))).birth =
      Nat.succ
        (normalizedBirthday
          (subMul
            (SurrealCore.add
              (coreMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame (n + 1)))
              (coreMul (LoFProgram.natPreGame (m + 1)) (LoFProgram.natPreGame n)))
            (coreMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame n)))) := by
  have hm :
      LoFProgram.natPreGame (m + 1) =
        ({ L := [LoFProgram.natPreGame m], R := [], birth := m + 1 } : PreGame) := by
    simp [LoFProgram.natPreGame, PreGame.build, PreGame.maxBirth, natPreGame_birth]
  have hn :
      LoFProgram.natPreGame (n + 1) =
        ({ L := [LoFProgram.natPreGame n], R := [], birth := n + 1 } : PreGame) := by
    simp [LoFProgram.natPreGame, PreGame.build, PreGame.maxBirth, natPreGame_birth]
  rw [hm, hn]
  unfold birthdayMul coreMul
  rw [mul_eq_explicit]
  simp [SurrealCore.isNullCut]
  rw [WellFounded.fix_eq (hwf := SurrealCore.mul._proof_1) (F := mulBodyExplicit)
    (x := (({ L := [LoFProgram.natPreGame m], R := [], birth := m + 1 } : PreGame),
      ({ L := [LoFProgram.natPreGame n], R := [], birth := n + 1 } : PreGame)))]
  simp [mulBodyExplicit, listBindMul, subMul, normalize,
    LoFProgram.normalize.eq_def, PreGame.build, PreGame.maxBirth]

/-- The natural-ladder multiplication lane is bounded by Fredman's recurrence. -/
theorem birthdayMul_natPreGame_birth_le : ∀ m n : Nat,
    (birthdayMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame n)).birth ≤ fredman m n
  | 0, n => by
      simp
  | m + 1, 0 => by
      simp
  | m + 1, n + 1 => by
      rw [birthdayMul_natPreGame_succ_succ_birth]
      have hsub :
          normalizedBirthday
              (subMul
                (SurrealCore.add
                  (coreMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame (n + 1)))
                  (coreMul (LoFProgram.natPreGame (m + 1)) (LoFProgram.natPreGame n)))
                (coreMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame n))) ≤
            (birthdayMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame (n + 1))).birth +
              (birthdayMul (LoFProgram.natPreGame (m + 1)) (LoFProgram.natPreGame n)).birth +
              (birthdayMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame n)).birth := by
        have hraw :=
          normalizedBirthday_sub_raw_le
            (SurrealCore.add
              (coreMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame (n + 1)))
              (coreMul (LoFProgram.natPreGame (m + 1)) (LoFProgram.natPreGame n)))
            (coreMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame n))
        have hadd :=
          birthdayAdd_birth_le
            (coreMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame (n + 1)))
            (coreMul (LoFProgram.natPreGame (m + 1)) (LoFProgram.natPreGame n))
        have hstep :
            normalizedBirthday
                (SurrealCore.add
                  (coreMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame (n + 1)))
                  (coreMul (LoFProgram.natPreGame (m + 1)) (LoFProgram.natPreGame n))) +
              normalizedBirthday
                (coreMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame n)) ≤
            (birthdayMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame (n + 1))).birth +
              (birthdayMul (LoFProgram.natPreGame (m + 1)) (LoFProgram.natPreGame n)).birth +
              (birthdayMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame n)).birth := by
          have hcore1 := normalizedBirthday_coreMul_natPreGame_eq_birthdayMul m (n + 1)
          have hcore2 := normalizedBirthday_coreMul_natPreGame_eq_birthdayMul (m + 1) n
          have hcore3 := normalizedBirthday_coreMul_natPreGame_eq_birthdayMul m n
          have hadd' :
              normalizedBirthday
                  (SurrealCore.add
                    (coreMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame (n + 1)))
                    (coreMul (LoFProgram.natPreGame (m + 1)) (LoFProgram.natPreGame n))) ≤
                (birthdayMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame (n + 1))).birth +
                  (birthdayMul (LoFProgram.natPreGame (m + 1)) (LoFProgram.natPreGame n)).birth := by
            rw [hcore1, hcore2] at hadd
            simpa [birthdayAdd] using hadd
          calc
            normalizedBirthday
                (SurrealCore.add
                  (coreMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame (n + 1)))
                  (coreMul (LoFProgram.natPreGame (m + 1)) (LoFProgram.natPreGame n))) +
              normalizedBirthday
                (coreMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame n))
                ≤
              ((birthdayMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame (n + 1))).birth +
                (birthdayMul (LoFProgram.natPreGame (m + 1)) (LoFProgram.natPreGame n)).birth) +
                  normalizedBirthday
                    (coreMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame n)) := by
                      exact Nat.add_le_add_right hadd' _
            _ = (birthdayMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame (n + 1))).birth +
                  (birthdayMul (LoFProgram.natPreGame (m + 1)) (LoFProgram.natPreGame n)).birth +
                  (birthdayMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame n)).birth := by
                    rw [hcore3]
        exact le_trans hraw hstep
      have hrec1 := birthdayMul_natPreGame_birth_le m (n + 1)
      have hrec2 := birthdayMul_natPreGame_birth_le (m + 1) n
      have hrec3 := birthdayMul_natPreGame_birth_le m n
      have hsum :
          (birthdayMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame (n + 1))).birth +
              (birthdayMul (LoFProgram.natPreGame (m + 1)) (LoFProgram.natPreGame n)).birth +
              (birthdayMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame n)).birth ≤
            fredman m (n + 1) + fredman (m + 1) n + fredman m n := by
        omega
      have : Nat.succ
          (normalizedBirthday
            (subMul
              (SurrealCore.add
                (coreMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame (n + 1)))
                (coreMul (LoFProgram.natPreGame (m + 1)) (LoFProgram.natPreGame n)))
              (coreMul (LoFProgram.natPreGame m) (LoFProgram.natPreGame n)))) ≤
          Nat.succ (fredman m (n + 1) + fredman (m + 1) n + fredman m n) := by
        exact Nat.succ_le_succ (le_trans hsub hsum)
      simpa [fredman]
        using this


end Birthday
end Surreal
end Numbers
end HeytingLean
