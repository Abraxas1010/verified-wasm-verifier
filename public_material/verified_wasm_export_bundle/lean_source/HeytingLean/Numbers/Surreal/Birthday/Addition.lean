import HeytingLean.Numbers.Surreal.Birthday.Negation

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace Birthday

private theorem add_natPreGame_zero_zero :
    SurrealCore.add SurrealCore.nullCut SurrealCore.nullCut =
      SurrealCore.PreGame.build [] [] := by
  conv_lhs => unfold SurrealCore.add
  simp [SurrealCore.nullCut, SurrealCore.PreGame.build]

private theorem add_natPreGame_zero_succ (n : Nat) :
    SurrealCore.add SurrealCore.nullCut (LoFProgram.natPreGame (n + 1)) =
      SurrealCore.PreGame.build [SurrealCore.add SurrealCore.nullCut (LoFProgram.natPreGame n)] [] := by
  conv_lhs => unfold SurrealCore.add
  simp [LoFProgram.natPreGame, SurrealCore.nullCut, SurrealCore.PreGame.build]

private theorem add_natPreGame_succ_zero (n : Nat) :
    SurrealCore.add (LoFProgram.natPreGame (n + 1)) SurrealCore.nullCut =
      SurrealCore.PreGame.build [SurrealCore.add (LoFProgram.natPreGame n) SurrealCore.nullCut] [] := by
  conv_lhs => unfold SurrealCore.add
  simp [LoFProgram.natPreGame, SurrealCore.nullCut, SurrealCore.PreGame.build]

private theorem add_natPreGame_succ_succ (m n : Nat) :
    SurrealCore.add (LoFProgram.natPreGame (m + 1)) (LoFProgram.natPreGame (n + 1)) =
      SurrealCore.PreGame.build
        [ SurrealCore.add (LoFProgram.natPreGame m) (LoFProgram.natPreGame (n + 1))
        , SurrealCore.add (LoFProgram.natPreGame (m + 1)) (LoFProgram.natPreGame n)] [] := by
  conv_lhs => unfold SurrealCore.add
  simp [LoFProgram.natPreGame, SurrealCore.PreGame.build]

private theorem sizeOf_lt_sizeOf_list_of_mem {x : BirthdayForm} {xs : List BirthdayForm} (h : x ∈ xs) :
    sizeOf x < sizeOf xs := by
  induction xs with
  | nil =>
      cases h
  | cons y ys ih =>
      cases h with
      | head =>
          have hpos : 0 < 1 + sizeOf ys := by
            have : 0 < sizeOf ys + 1 := Nat.succ_pos _
            simpa [Nat.add_comm] using this
          have hlt : sizeOf x < sizeOf x + (1 + sizeOf ys) :=
            Nat.lt_add_of_pos_right hpos
          simpa [List.cons.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt
      | tail _ hx =>
          have hlt : sizeOf x < sizeOf ys := ih hx
          have hpos : 0 < 1 + sizeOf y := by
            have : 0 < sizeOf y + 1 := Nat.succ_pos _
            simpa [Nat.add_comm] using this
          have hlt' : sizeOf ys < sizeOf ys + (1 + sizeOf y) :=
            Nat.lt_add_of_pos_right hpos
          have hcons : sizeOf ys < sizeOf (y :: ys) := by
            simpa [List.cons.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt'
          exact Nat.lt_trans hlt hcons

private theorem sizeOf_lt_sizeOf_left
    {L R : List BirthdayForm} {birth : Nat} {g : BirthdayForm} (h : g ∈ L) :
    sizeOf g < sizeOf ({ L := L, R := R, birth := birth } : BirthdayForm) := by
  have hmem : sizeOf g < sizeOf L := sizeOf_lt_sizeOf_list_of_mem h
  have hpos : 0 < 1 + sizeOf R + sizeOf birth := by
    have : 0 < Nat.succ (sizeOf R + sizeOf birth) := Nat.succ_pos _
    simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  have hlt : sizeOf L < sizeOf L + (1 + sizeOf R + sizeOf birth) :=
    Nat.lt_add_of_pos_right hpos
  have hL : sizeOf L < sizeOf ({ L := L, R := R, birth := birth } : BirthdayForm) := by
    simpa [SurrealCore.PreGame.mk.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt
  exact Nat.lt_trans hmem hL

private theorem sizeOf_lt_sizeOf_right
    {L R : List BirthdayForm} {birth : Nat} {g : BirthdayForm} (h : g ∈ R) :
    sizeOf g < sizeOf ({ L := L, R := R, birth := birth } : BirthdayForm) := by
  have hmem : sizeOf g < sizeOf R := sizeOf_lt_sizeOf_list_of_mem h
  have hpos : 0 < 1 + sizeOf L + sizeOf birth := by
    have : 0 < Nat.succ (sizeOf L + sizeOf birth) := Nat.succ_pos _
    simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  have hlt : sizeOf R < sizeOf R + (1 + sizeOf L + sizeOf birth) :=
    Nat.lt_add_of_pos_right hpos
  have hR : sizeOf R < sizeOf ({ L := L, R := R, birth := birth } : BirthdayForm) := by
    simpa [SurrealCore.PreGame.mk.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt
  exact Nat.lt_trans hmem hR

/-- Birthday-normalized addition is subadditive on the normalized finite carrier. -/
theorem birthdayAdd_birth_le : ∀ x y : BirthdayForm,
    (birthdayAdd x y).birth ≤ normalizedBirthday x + normalizedBirthday y
  | { L := xL, R := xR, birth := xb }, { L := yL, R := yR, birth := yb } => by
      let x : BirthdayForm := { L := xL, R := xR, birth := xb }
      let y : BirthdayForm := { L := yL, R := yR, birth := yb }
      let leftRaw : List BirthdayForm :=
        xL.map (fun xl => SurrealCore.add xl y) ++
          yL.map (fun yl => SurrealCore.add x yl)
      let rightRaw : List BirthdayForm :=
        xR.map (fun xr => SurrealCore.add xr y) ++
          yR.map (fun yr => SurrealCore.add x yr)
      let leftNorm : List BirthdayForm := leftRaw.map normalize
      let rightNorm : List BirthdayForm := rightRaw.map normalize
      change (birthdayAdd x y).birth ≤ normalizedBirthday x + normalizedBirthday y
      by_cases hEmpty : (xL = [] ∧ xR = []) ∧ (yL = [] ∧ yR = [])
      · rcases hEmpty with ⟨⟨hxL, hxR⟩, ⟨hyL, hyR⟩⟩
        have hxNorm : normalizedBirthday x = 0 := by
          unfold normalizedBirthday
          unfold normalize
          rw [LoFProgram.normalize.eq_def]
          simp [x, hxL, hxR, SurrealCore.birthday, SurrealCore.nullCut]
        have hyNorm : normalizedBirthday y = 0 := by
          unfold normalizedBirthday
          unfold normalize
          rw [LoFProgram.normalize.eq_def]
          simp [y, hyL, hyR, SurrealCore.birthday, SurrealCore.nullCut]
        have hadd : birthdayAdd x y = SurrealCore.nullCut := by
          unfold birthdayAdd
          rw [SurrealCore.add.eq_1]
          simp [x, y, hxL, hxR, hyL, hyR, SurrealCore.PreGame.build]
          unfold normalize
          rw [LoFProgram.normalize.eq_def]
        rw [hadd, hxNorm, hyNorm]
        decide
      · have hSupport : xL ≠ [] ∨ xR ≠ [] ∨ yL ≠ [] ∨ yR ≠ [] := by
          by_contra hSupport
          push_neg at hSupport
          exact hEmpty ⟨⟨hSupport.1, hSupport.2.1⟩, ⟨hSupport.2.2.1, hSupport.2.2.2⟩⟩
        have hSumPos : 0 < normalizedBirthday x + normalizedBirthday y := by
          rcases hSupport with hxL | hxR | hyL | hyR
          · exact Nat.add_pos_left (show 0 < normalizedBirthday x by
              rw [normalizedBirthday_eq_of_nonempty (birth := xb) (Or.inl hxL)]
              exact Nat.succ_pos _) _
          · exact Nat.add_pos_left (show 0 < normalizedBirthday x by
              rw [normalizedBirthday_eq_of_nonempty (birth := xb) (Or.inr hxR)]
              exact Nat.succ_pos _) _
          · exact Nat.add_pos_right _ (show 0 < normalizedBirthday y by
              rw [normalizedBirthday_eq_of_nonempty (birth := yb) (Or.inl hyL)]
              exact Nat.succ_pos _)
          · exact Nat.add_pos_right _ (show 0 < normalizedBirthday y by
              rw [normalizedBirthday_eq_of_nonempty (birth := yb) (Or.inr hyR)]
              exact Nat.succ_pos _)
        have hRawNonempty : leftRaw ≠ [] ∨ rightRaw ≠ [] := by
          rcases hSupport with hxL | hxR | hyL | hyR
          · left
            intro h
            apply hxL
            have hlen : xL.length + yL.length = 0 := by
              simpa [leftRaw] using congrArg List.length h
            have hxlen : xL.length = 0 := by omega
            exact List.length_eq_zero_iff.mp hxlen
          · right
            intro h
            apply hxR
            have hlen : xR.length + yR.length = 0 := by
              simpa [rightRaw] using congrArg List.length h
            have hxlen : xR.length = 0 := by omega
            exact List.length_eq_zero_iff.mp hxlen
          · left
            intro h
            apply hyL
            have hlen : xL.length + yL.length = 0 := by
              simpa [leftRaw] using congrArg List.length h
            have hylen : yL.length = 0 := by omega
            exact List.length_eq_zero_iff.mp hylen
          · right
            intro h
            apply hyR
            have hlen : xR.length + yR.length = 0 := by
              simpa [rightRaw] using congrArg List.length h
            have hylen : yR.length = 0 := by omega
            exact List.length_eq_zero_iff.mp hylen
        have hLeftBound : SurrealCore.PreGame.maxBirth leftNorm < normalizedBirthday x + normalizedBirthday y := by
          apply maxBirth_lt_of_forall hSumPos
          intro z hz
          rcases List.mem_map.mp hz with ⟨z', hz', rfl⟩
          rcases List.mem_append.mp hz' with hz' | hz'
          · rcases List.mem_map.mp hz' with ⟨xl, hxl, rfl⟩
            have hrec := birthdayAdd_birth_le xl y
            exact lt_of_le_of_lt hrec (Nat.add_lt_add_right (normalizedBirthday_left_lt (x := x) hxl) _)
          · rcases List.mem_map.mp hz' with ⟨yl, hyl, rfl⟩
            have hrec := birthdayAdd_birth_le x yl
            exact lt_of_le_of_lt hrec (Nat.add_lt_add_left (normalizedBirthday_left_lt (x := y) hyl) _)
        have hRightBound : SurrealCore.PreGame.maxBirth rightNorm < normalizedBirthday x + normalizedBirthday y := by
          apply maxBirth_lt_of_forall hSumPos
          intro z hz
          rcases List.mem_map.mp hz with ⟨z', hz', rfl⟩
          rcases List.mem_append.mp hz' with hz' | hz'
          · rcases List.mem_map.mp hz' with ⟨xr, hxr, rfl⟩
            have hrec := birthdayAdd_birth_le xr y
            exact lt_of_le_of_lt hrec (Nat.add_lt_add_right (normalizedBirthday_right_lt (x := x) hxr) _)
          · rcases List.mem_map.mp hz' with ⟨yr, hyr, rfl⟩
            have hrec := birthdayAdd_birth_le x yr
            exact lt_of_le_of_lt hrec (Nat.add_lt_add_left (normalizedBirthday_right_lt (x := y) hyr) _)
        have hBirth :
            (birthdayAdd x y).birth =
              Nat.succ (Nat.max (SurrealCore.PreGame.maxBirth leftNorm) (SurrealCore.PreGame.maxBirth rightNorm)) := by
          change normalizedBirthday (SurrealCore.add x y) =
            Nat.succ (Nat.max (SurrealCore.PreGame.maxBirth leftNorm) (SurrealCore.PreGame.maxBirth rightNorm))
          rw [SurrealCore.add.eq_1]
          simp only [x, y]
          change normalizedBirthday
              ({ L := leftRaw, R := rightRaw,
                 birth := (SurrealCore.PreGame.build leftRaw rightRaw).birth } : BirthdayForm) =
            Nat.succ (Nat.max (SurrealCore.PreGame.maxBirth leftNorm) (SurrealCore.PreGame.maxBirth rightNorm))
          rw [normalizedBirthday_eq_of_nonempty
            (birth := (SurrealCore.PreGame.build leftRaw rightRaw).birth) hRawNonempty]
        rw [hBirth]
        exact Nat.succ_le_of_lt ((Nat.max_lt).2 ⟨hLeftBound, hRightBound⟩)
termination_by x y => (sizeOf x, sizeOf y)
decreasing_by
  all_goals
    first
    | exact Prod.Lex.left (b₁ := sizeOf y) (b₂ := sizeOf y)
        (sizeOf_lt_sizeOf_left (birth := xb) (R := xR) hxl)
    | exact Prod.Lex.right (a := sizeOf x)
        (sizeOf_lt_sizeOf_left (birth := yb) (R := yR) hyl)
    | exact Prod.Lex.left (b₁ := sizeOf y) (b₂ := sizeOf y)
        (sizeOf_lt_sizeOf_right (birth := xb) (L := xL) hxr)
    | exact Prod.Lex.right (a := sizeOf x)
        (sizeOf_lt_sizeOf_right (birth := yb) (L := yL) hyr)

/-- On the canonical natural ladder, birthday-normalized addition has the expected additive day. -/
@[simp] theorem birthdayAdd_natPreGame_birth : ∀ m n : Nat,
    (birthdayAdd (LoFProgram.natPreGame m) (LoFProgram.natPreGame n)).birth = m + n
  | 0, 0 => by
      unfold birthdayAdd
      rw [show LoFProgram.natPreGame 0 = SurrealCore.nullCut by rfl]
      rw [add_natPreGame_zero_zero]
      unfold normalize
      rw [LoFProgram.normalize.eq_def]
      rfl
  | 0, n + 1 => by
      unfold birthdayAdd
      rw [show LoFProgram.natPreGame 0 = SurrealCore.nullCut by rfl]
      rw [add_natPreGame_zero_succ, normalize_build_single_left]
      have ih := birthdayAdd_natPreGame_birth 0 n
      simpa [SurrealCore.PreGame.build, SurrealCore.PreGame.maxBirth] using congrArg Nat.succ ih
  | m + 1, 0 => by
      unfold birthdayAdd
      rw [show LoFProgram.natPreGame 0 = SurrealCore.nullCut by rfl]
      rw [add_natPreGame_succ_zero, normalize_build_single_left]
      have ih := birthdayAdd_natPreGame_birth m 0
      simpa [SurrealCore.PreGame.build, SurrealCore.PreGame.maxBirth] using congrArg Nat.succ ih
  | m + 1, n + 1 => by
      unfold birthdayAdd
      rw [add_natPreGame_succ_succ, normalize_build_left_cons]
      have hLeft :
          (normalize (SurrealCore.add (LoFProgram.natPreGame m) (LoFProgram.natPreGame (n + 1)))).birth =
            m + (n + 1) := by
        simpa [birthdayAdd] using birthdayAdd_natPreGame_birth m (n + 1)
      have hRight :
          (normalize (SurrealCore.add (LoFProgram.natPreGame (m + 1)) (LoFProgram.natPreGame n))).birth =
            (m + 1) + n := by
        simpa [birthdayAdd] using birthdayAdd_natPreGame_birth (m + 1) n
      simp [SurrealCore.PreGame.build, SurrealCore.PreGame.maxBirth, hLeft, hRight,
        Nat.add_left_comm, Nat.add_comm]

@[simp] theorem birthdayAdd_natPreGame_zero_left (n : Nat) :
    (birthdayAdd SurrealCore.nullCut (LoFProgram.natPreGame n)).birth = n := by
  simpa [LoFProgram.natPreGame] using birthdayAdd_natPreGame_birth 0 n

@[simp] theorem birthdayAdd_natPreGame_zero_right (n : Nat) :
    (birthdayAdd (LoFProgram.natPreGame n) SurrealCore.nullCut).birth = n := by
  simpa [LoFProgram.natPreGame] using birthdayAdd_natPreGame_birth n 0

theorem normalizedBirthday_sub_raw_le (x y : BirthdayForm) :
    normalizedBirthday (SurrealCore.add x (SurrealCore.neg y)) ≤ normalizedBirthday x + normalizedBirthday y := by
  have h := birthdayAdd_birth_le x (SurrealCore.neg y)
  rw [normalizedBirthday_neg] at h
  simpa [birthdayAdd] using h

theorem birthdaySub_birth_le (x y : BirthdayForm) :
    (birthdaySub x y).birth ≤ normalizedBirthday x + normalizedBirthday y := by
  have h := birthdayAdd_birth_le x (normalize (SurrealCore.neg y))
  rw [normalizedBirthday_normalize, normalizedBirthday_neg] at h
  simpa [birthdaySub, birthdayAdd, birthdayNeg] using h

end Birthday
end Surreal
end Numbers
end HeytingLean
