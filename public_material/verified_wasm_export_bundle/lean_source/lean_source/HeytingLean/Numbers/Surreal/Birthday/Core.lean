import HeytingLean.Automation.QwenGenerated
import HeytingLean.Numbers.Surreal.LoFProgram

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace Birthday

open HeytingLean.Numbers.SurrealCore

/-- The raw finite pre-game carrier reused by the birthday arithmetic lane. -/
abbrev BirthdayForm := PreGame

/-- Normalize a raw pre-game by recomputing its birthdays bottom-up. -/
abbrev normalize : BirthdayForm → BirthdayForm := LoFProgram.normalize

/-- The birthday seen through the normalized finite carrier. -/
def normalizedBirthday (g : BirthdayForm) : Nat :=
  SurrealCore.birthday (normalize g)

/-- Negation wrapped with birthday normalization. -/
noncomputable def birthdayNeg (g : BirthdayForm) : BirthdayForm :=
  normalize (SurrealCore.neg g)

/-- Addition wrapped with birthday normalization. -/
noncomputable def birthdayAdd (x y : BirthdayForm) : BirthdayForm :=
  normalize (SurrealCore.add x y)

/-- Subtraction wrapped with birthday normalization. -/
noncomputable def birthdaySub (x y : BirthdayForm) : BirthdayForm :=
  birthdayAdd x (birthdayNeg y)

/-- Multiplication wrapped with birthday normalization. -/
noncomputable def birthdayMul (x y : BirthdayForm) : BirthdayForm :=
  normalize (SurrealCore.mul x y)

/-- The immediate option set of a raw finite pre-game. -/
def parents (x : BirthdayForm) : List BirthdayForm :=
  x.L ++ x.R

@[simp] theorem normalizedBirthday_eq (g : BirthdayForm) :
    normalizedBirthday g = (normalize g).birth := by
  rfl

@[simp] theorem parents_nullCut : parents SurrealCore.nullCut = [] := by
  rfl

@[simp] theorem normalizedBirthday_nullCut :
    normalizedBirthday SurrealCore.nullCut = 0 := by
  unfold normalizedBirthday normalize
  rw [LoFProgram.normalize.eq_def]
  rfl

@[simp] theorem normalize_nullCut :
    normalize SurrealCore.nullCut = SurrealCore.nullCut := by
  unfold normalize
  rw [LoFProgram.normalize.eq_def]
  rfl

@[simp] theorem normalize_build_left_cons (l : BirthdayForm) (ls R : List BirthdayForm) :
    normalize (PreGame.build (l :: ls) R) =
      PreGame.build ((l :: ls).map normalize) (R.map normalize) := by
  unfold normalize
  rw [LoFProgram.normalize.eq_def]
  rfl

@[simp] theorem normalize_build_right_cons (r : BirthdayForm) (rs : List BirthdayForm) :
    normalize (PreGame.build [] (r :: rs)) =
      PreGame.build [] ((r :: rs).map normalize) := by
  unfold normalize
  rw [LoFProgram.normalize.eq_def]
  rfl

@[simp] theorem maxBirth_singleton (g : BirthdayForm) :
    PreGame.maxBirth [g] = g.birth := by
  simp [PreGame.maxBirth]

@[simp] theorem normalize_build_single_left (g : BirthdayForm) :
    normalize (PreGame.build [g] []) = PreGame.build [normalize g] [] := by
  unfold normalize
  rw [LoFProgram.normalize.eq_def]
  rfl

@[simp] theorem normalize_build_single_right (g : BirthdayForm) :
    normalize (PreGame.build [] [g]) = PreGame.build [] [normalize g] := by
  unfold normalize
  rw [LoFProgram.normalize.eq_def]
  rfl

private theorem le_foldl_max (acc : Nat) (xs : List BirthdayForm) :
    acc ≤ xs.foldl (fun a g => Nat.max a g.birth) acc := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      exact le_trans (Nat.le_max_left _ _) (by
        simpa [List.foldl] using ih (Nat.max acc x.birth))

private theorem birth_le_foldl_max_of_mem {xs : List BirthdayForm} {g : BirthdayForm}
    (acc : Nat) (h : g ∈ xs) :
    g.birth ≤ xs.foldl (fun a g => Nat.max a g.birth) acc := by
  induction xs generalizing acc with
  | nil =>
      cases h
  | cons x xs ih =>
      cases h with
      | head =>
          exact le_trans (Nat.le_max_right _ _) (by
            simpa [List.foldl] using le_foldl_max (Nat.max acc g.birth) xs)
      | tail _ hxs =>
          simpa [List.foldl] using ih (Nat.max acc x.birth) hxs

private theorem birth_le_maxBirth_of_mem {xs : List BirthdayForm} {g : BirthdayForm}
    (h : g ∈ xs) :
    g.birth ≤ PreGame.maxBirth xs := by
  simpa [PreGame.maxBirth] using birth_le_foldl_max_of_mem 0 h

theorem normalizedBirthday_eq_of_nonempty
    {L R : List BirthdayForm} {birth : Nat} (h : L ≠ [] ∨ R ≠ []) :
    normalizedBirthday ({ L := L, R := R, birth := birth } : BirthdayForm) =
      Nat.succ (Nat.max (PreGame.maxBirth (L.map normalize)) (PreGame.maxBirth (R.map normalize))) := by
  cases L with
  | nil =>
      cases R with
      | nil =>
          cases h with
          | inl hL => cases (hL rfl)
          | inr hR => cases (hR rfl)
      | cons r rs =>
          simp [normalizedBirthday, normalize, LoFProgram.normalize.eq_def]
  | cons l ls =>
      simp [normalizedBirthday, normalize, LoFProgram.normalize.eq_def]

theorem normalizedBirthday_le_maxBirth_left_of_mem
    {L : List BirthdayForm} {g : BirthdayForm} (h : g ∈ L) :
    normalizedBirthday g ≤ PreGame.maxBirth (L.map normalize) := by
  have hmem : normalize g ∈ L.map normalize := List.mem_map.mpr ⟨g, h, rfl⟩
  simpa [normalizedBirthday_eq] using birth_le_maxBirth_of_mem hmem

theorem normalizedBirthday_le_maxBirth_right_of_mem
    {R : List BirthdayForm} {g : BirthdayForm} (h : g ∈ R) :
    normalizedBirthday g ≤ PreGame.maxBirth (R.map normalize) := by
  have hmem : normalize g ∈ R.map normalize := List.mem_map.mpr ⟨g, h, rfl⟩
  simpa [normalizedBirthday_eq] using birth_le_maxBirth_of_mem hmem

theorem normalizedBirthday_lt_of_mem_left
    {L R : List BirthdayForm} {birth : Nat} {g : BirthdayForm} (h : g ∈ L) :
    normalizedBirthday g < normalizedBirthday ({ L := L, R := R, birth := birth } : BirthdayForm) := by
  have hnonempty : L ≠ [] ∨ R ≠ [] := Or.inl (by
    intro hL
    rw [hL] at h
    cases h)
  rw [normalizedBirthday_eq_of_nonempty hnonempty]
  exact Nat.lt_succ_of_le <|
    le_trans (normalizedBirthday_le_maxBirth_left_of_mem h)
      (Nat.le_max_left _ _)

theorem normalizedBirthday_lt_of_mem_right
    {L R : List BirthdayForm} {birth : Nat} {g : BirthdayForm} (h : g ∈ R) :
    normalizedBirthday g < normalizedBirthday ({ L := L, R := R, birth := birth } : BirthdayForm) := by
  have hnonempty : L ≠ [] ∨ R ≠ [] := Or.inr (by
    intro hR
    rw [hR] at h
    cases h)
  rw [normalizedBirthday_eq_of_nonempty hnonempty]
  exact Nat.lt_succ_of_le <|
    le_trans (normalizedBirthday_le_maxBirth_right_of_mem h)
      (Nat.le_max_right _ _)

theorem normalizedBirthday_left_lt {x g : BirthdayForm} (h : g ∈ x.L) :
    normalizedBirthday g < normalizedBirthday x := by
  cases x with
  | mk L R birth =>
      simpa using (normalizedBirthday_lt_of_mem_left (birth := birth) (R := R) h)

theorem normalizedBirthday_right_lt {x g : BirthdayForm} (h : g ∈ x.R) :
    normalizedBirthday g < normalizedBirthday x := by
  cases x with
  | mk L R birth =>
      simpa using (normalizedBirthday_lt_of_mem_right (birth := birth) (L := L) h)

private theorem foldl_max_le_of_forall
    {xs : List BirthdayForm} {f : BirthdayForm → BirthdayForm} {n acc : Nat}
    (hacc : acc ≤ n) (h : ∀ x ∈ xs, (f x).birth ≤ n) :
    (xs.map f).foldl (fun a g => Nat.max a g.birth) acc ≤ n := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons x xs ih =>
      have hstep : Nat.max acc (f x).birth ≤ n := (Nat.max_le).2 ⟨hacc, h x (by simp)⟩
      simpa [List.foldl] using ih hstep (by
        intro y hy
        exact h y (by simp [hy]))

theorem maxBirth_map_le_of_forall {xs : List BirthdayForm} {f : BirthdayForm → BirthdayForm}
    {n : Nat} (h : ∀ x ∈ xs, (f x).birth ≤ n) :
    PreGame.maxBirth (xs.map f) ≤ n := by
  simpa [PreGame.maxBirth] using foldl_max_le_of_forall (acc := 0) (by simp) h

private theorem foldl_max_lt_of_forall
    {xs : List BirthdayForm} {n acc : Nat}
    (hacc : acc < n) (h : ∀ x ∈ xs, x.birth < n) :
    xs.foldl (fun a g => Nat.max a g.birth) acc < n := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons x xs ih =>
      have hstep : Nat.max acc x.birth < n := (Nat.max_lt).2 ⟨hacc, h x (by simp)⟩
      simpa [List.foldl] using ih hstep (by
        intro y hy
        exact h y (by simp [hy]))

theorem maxBirth_lt_of_forall {xs : List BirthdayForm} {n : Nat}
    (hpos : 0 < n) (h : ∀ x ∈ xs, x.birth < n) :
    PreGame.maxBirth xs < n := by
  simpa [PreGame.maxBirth] using foldl_max_lt_of_forall (acc := 0) hpos h

private theorem foldl_max_eq_of_pointwise
    {xs : List BirthdayForm} {f g : BirthdayForm → BirthdayForm} (acc : Nat)
    (h : ∀ x ∈ xs, (f x).birth = (g x).birth) :
    (xs.map f).foldl (fun a g => Nat.max a g.birth) acc =
      (xs.map g).foldl (fun a g => Nat.max a g.birth) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      simpa [List.foldl, h x (by simp)] using ih (Nat.max acc (g x).birth) (by
        intro y hy
        exact h y (by simp [hy]))

theorem maxBirth_map_eq_of_pointwise
    {xs : List BirthdayForm} {f g : BirthdayForm → BirthdayForm}
    (h : ∀ x ∈ xs, (f x).birth = (g x).birth) :
    PreGame.maxBirth (xs.map f) = PreGame.maxBirth (xs.map g) := by
  simpa [PreGame.maxBirth] using foldl_max_eq_of_pointwise (acc := 0) h

@[simp] theorem normalizedBirthday_normalize : ∀ g : BirthdayForm,
    normalizedBirthday (normalize g) = normalizedBirthday g
  | { L := L, R := R, birth := birth } => by
      by_cases hEmpty : L = [] ∧ R = []
      · rcases hEmpty with ⟨hL, hR⟩
        simp [normalizedBirthday, normalize, LoFProgram.normalize.eq_def, hL, hR,
          SurrealCore.nullCut, SurrealCore.birthday]
      · have hnonempty : L ≠ [] ∨ R ≠ [] := by
          by_cases hL : L = []
          · right
            intro hR
            exact hEmpty ⟨hL, hR⟩
          · exact Or.inl hL
        have hLmax :
            SurrealCore.PreGame.maxBirth (List.map normalize (List.map normalize L)) =
              SurrealCore.PreGame.maxBirth (List.map normalize L) := by
          simpa [List.map_map] using
            (maxBirth_map_eq_of_pointwise
              (xs := L) (f := fun x => normalize (normalize x)) (g := normalize) (by
                intro x hx
                simpa [normalizedBirthday, SurrealCore.birthday] using normalizedBirthday_normalize x))
        have hRmax :
            SurrealCore.PreGame.maxBirth (List.map normalize (List.map normalize R)) =
              SurrealCore.PreGame.maxBirth (List.map normalize R) := by
          simpa [List.map_map] using
            (maxBirth_map_eq_of_pointwise
              (xs := R) (f := fun x => normalize (normalize x)) (g := normalize) (by
                intro x hx
                simpa [normalizedBirthday, SurrealCore.birthday] using normalizedBirthday_normalize x))
        have hnorm : normalize ({ L := L, R := R, birth := birth } : BirthdayForm) =
            SurrealCore.PreGame.build (L.map normalize) (R.map normalize) := by
          cases L with
          | nil =>
              cases R with
              | nil => exact False.elim (hEmpty ⟨rfl, rfl⟩)
              | cons r rs =>
                  simp [normalize, LoFProgram.normalize.eq_def]
          | cons l ls =>
              simp [normalize, LoFProgram.normalize.eq_def]
        rw [hnorm]
        change normalizedBirthday
            ({ L := L.map normalize, R := R.map normalize,
               birth := (SurrealCore.PreGame.build (L.map normalize) (R.map normalize)).birth } :
                BirthdayForm) =
          normalizedBirthday ({ L := L, R := R, birth := birth } : BirthdayForm)
        rw [normalizedBirthday_eq_of_nonempty
          (birth := (SurrealCore.PreGame.build (L.map normalize) (R.map normalize)).birth)]
        · rw [normalizedBirthday_eq_of_nonempty (birth := birth) hnonempty]
          rw [hLmax, hRmax]
        · cases hnonempty with
          | inl hL => exact Or.inl (by simpa using hL)
          | inr hR => exact Or.inr (by simpa using hR)

theorem normalizedBirthday_single_left (g : BirthdayForm) :
    normalizedBirthday ({ L := [g], R := [], birth := g.birth + 1 } : BirthdayForm) =
      Nat.succ (normalizedBirthday g) := by
  rw [normalizedBirthday_eq_of_nonempty (birth := g.birth + 1) (Or.inl (by simp))]
  simp [SurrealCore.PreGame.maxBirth, normalizedBirthday_eq]

end Birthday
end Surreal
end Numbers
end HeytingLean
