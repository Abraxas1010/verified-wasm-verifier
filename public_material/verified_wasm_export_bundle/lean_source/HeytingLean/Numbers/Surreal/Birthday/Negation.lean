import HeytingLean.Numbers.Surreal.Birthday.CanonicalDyadic

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace Birthday

@[simp] theorem normalizedBirthday_neg : ∀ g : BirthdayForm,
    normalizedBirthday (SurrealCore.neg g) = normalizedBirthday g
  | { L := L, R := R, birth := birth } => by
      by_cases hEmpty : L = [] ∧ R = []
      · rcases hEmpty with ⟨hL, hR⟩
        simp [normalizedBirthday, normalize, LoFProgram.normalize.eq_def, SurrealCore.neg,
          hL, hR, SurrealCore.PreGame.build, SurrealCore.nullCut, SurrealCore.birthday]
      · have hnonempty : L ≠ [] ∨ R ≠ [] := by
          by_cases hL : L = []
          · right
            intro hR
            exact hEmpty ⟨hL, hR⟩
          · exact Or.inl hL
        have hnegNonempty : (R.map SurrealCore.neg) ≠ [] ∨ (L.map SurrealCore.neg) ≠ [] := by
          cases hnonempty with
          | inl hL =>
              right
              simpa using hL
          | inr hR =>
              left
              simpa using hR
        have hRmax :
            SurrealCore.PreGame.maxBirth (List.map normalize (R.map SurrealCore.neg)) =
              SurrealCore.PreGame.maxBirth (R.map normalize) := by
          simpa [List.map_map] using
            (maxBirth_map_eq_of_pointwise
              (xs := R) (f := fun x => normalize (SurrealCore.neg x)) (g := normalize) (by
                intro x hx
                simpa [normalizedBirthday, SurrealCore.birthday] using normalizedBirthday_neg x))
        have hLmax :
            SurrealCore.PreGame.maxBirth (List.map normalize (L.map SurrealCore.neg)) =
              SurrealCore.PreGame.maxBirth (L.map normalize) := by
          simpa [List.map_map] using
            (maxBirth_map_eq_of_pointwise
              (xs := L) (f := fun x => normalize (SurrealCore.neg x)) (g := normalize) (by
                intro x hx
                simpa [normalizedBirthday, SurrealCore.birthday] using normalizedBirthday_neg x))
        rw [show SurrealCore.neg ({ L := L, R := R, birth := birth } : BirthdayForm) =
            SurrealCore.PreGame.build (R.map SurrealCore.neg) (L.map SurrealCore.neg) by
              simp [SurrealCore.neg]]
        change normalizedBirthday
            ({ L := R.map SurrealCore.neg, R := L.map SurrealCore.neg,
               birth := (SurrealCore.PreGame.build (R.map SurrealCore.neg) (L.map SurrealCore.neg)).birth } :
              BirthdayForm) =
          normalizedBirthday ({ L := L, R := R, birth := birth } : BirthdayForm)
        rw [normalizedBirthday_eq_of_nonempty
          (birth := (SurrealCore.PreGame.build (R.map SurrealCore.neg) (L.map SurrealCore.neg)).birth)
          hnegNonempty]
        rw [normalizedBirthday_eq_of_nonempty (birth := birth) hnonempty]
        rw [hLmax, hRmax]
        simp [Nat.max_comm]

/-- Birthday-normalized negation preserves the normalized day exactly. -/
@[simp] theorem birthdayNeg_birth (g : BirthdayForm) :
    (birthdayNeg g).birth = normalizedBirthday g := by
  simpa [birthdayNeg, normalizedBirthday] using normalizedBirthday_neg g

/-- Canonical positive and negative integer ladders share the same birthday. -/
@[simp] theorem normalizedBirthday_natPreGame_succ_eq_negNatPreGame
    (n : Nat) :
    normalizedBirthday (LoFProgram.natPreGame (n + 1)) =
      normalizedBirthday (LoFProgram.negNatPreGame n) := by
  simp

/-- Integer birthdays depend only on absolute value, so sign-flip preserves them. -/
@[simp] theorem normalizedBirthday_intPreGame_neg (z : Int) :
    normalizedBirthday (LoFProgram.intPreGame (-z)) =
      normalizedBirthday (LoFProgram.intPreGame z) := by
  rw [normalizedBirthday_intPreGame, normalizedBirthday_intPreGame, Int.natAbs_neg]

/-- The canonical integer lane is sign-symmetric at the birthday level. -/
theorem normalizedBirthday_intPreGame_signInvariant (z : Int) :
    normalizedBirthday (LoFProgram.intPreGame z) = Int.natAbs z ∧
      normalizedBirthday (LoFProgram.intPreGame (-z)) = Int.natAbs z := by
  constructor
  · rw [normalizedBirthday_intPreGame]
  · rw [normalizedBirthday_intPreGame, Int.natAbs_neg]

end Birthday
end Surreal
end Numbers
end HeytingLean
