import HeytingLean.ModalCategorySets.Framework.InfiniteGuardedButtons
import HeytingLean.ModalCategorySets.Framework.SubstitutionValidity
import HeytingLean.ModalCategorySets.Validities.BooleanFrames

namespace HeytingLean.ModalCategorySets.Framework

open scoped Classical
open HeytingLean.ModalCategorySets.Framework.Equality
open HeytingLean.ModalCategorySets.Propositional
open HeytingLean.ModalCategorySets.Validities

universe u v

namespace Buttons

noncomputable section

def guardedTruthSetAll {α : Type u} [Infinite α] (ρ : Valuation α) (n : Nat) : Finset (Fin n) :=
  Finset.univ.filter fun i => HoldsInfAll ρ (guardedButton i)

def guardedTruthSetSurj {α : Type u} [Infinite α] (ρ : Valuation α) (n : Nat) : Finset (Fin n) :=
  Finset.univ.filter fun i => HoldsInfSurj ρ (guardedButton i)

@[simp] theorem mem_guardedTruthSetAll_iff {α : Type u} [Infinite α] (ρ : Valuation α)
    {n : Nat} {i : Fin n} :
    i ∈ guardedTruthSetAll ρ n ↔ HoldsInfAll ρ (guardedButton i) := by
  simp [guardedTruthSetAll]

@[simp] theorem mem_guardedTruthSetSurj_iff {α : Type u} [Infinite α] (ρ : Valuation α)
    {n : Nat} {i : Fin n} :
    i ∈ guardedTruthSetSurj ρ n ↔ HoldsInfSurj ρ (guardedButton i) := by
  simp [guardedTruthSetSurj]

theorem guardedTruthSetAll_pattern {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat} :
    GuardedButtonPatternAll ρ (guardedTruthSetAll ρ n) := by
  intro i
  simp [guardedTruthSetAll]

theorem guardedTruthSetSurj_pattern {α : Type u} [Infinite α] (ρ : Valuation α) {n : Nat} :
    GuardedButtonPatternSurj ρ (guardedTruthSetSurj ρ n) := by
  intro i
  simp [guardedTruthSetSurj]

theorem guardedTruthSetAll_eq_of_pattern {α : Type u} [Infinite α] (ρ : Valuation α)
    {n : Nat} {s : Finset (Fin n)} (hPattern : GuardedButtonPatternAll ρ s) :
    guardedTruthSetAll ρ n = s := by
  ext i
  simpa [guardedTruthSetAll] using hPattern i

theorem guardedTruthSetSurj_eq_of_pattern {α : Type u} [Infinite α] (ρ : Valuation α)
    {n : Nat} {s : Finset (Fin n)} (hPattern : GuardedButtonPatternSurj ρ s) :
    guardedTruthSetSurj ρ n = s := by
  ext i
  simpa [guardedTruthSetSurj] using hPattern i

theorem guardedTruthSetAll_mono {α β : Type u} [Infinite α] [Infinite β]
    (ρ : Valuation α) {n : Nat} (f : α → β) :
    guardedTruthSetAll ρ n ⊆ guardedTruthSetAll (fun i => f (ρ i)) n := by
  intro i hi
  rw [mem_guardedTruthSetAll_iff] at hi ⊢
  have hBox := holdsInfAll_guardedButton_persistent (ρ := ρ) i hi
  exact hBox β (show Infinite β from inferInstance) f trivial

theorem guardedTruthSetSurj_mono {α β : Type u} [Infinite α] [Infinite β]
    (ρ : Valuation α) {n : Nat} (f : α → β) (hf : Function.Surjective f) :
    guardedTruthSetSurj ρ n ⊆ guardedTruthSetSurj (fun i => f (ρ i)) n := by
  intro i hi
  rw [mem_guardedTruthSetSurj_iff] at hi ⊢
  have hBox := holdsInfSurj_guardedButton_persistent (ρ := ρ) i hi
  exact hBox β (show Infinite β from inferInstance) f hf

theorem exists_allFunctions_guardedTruthSet_above {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} (t : Finset (Fin n))
    (hst : guardedTruthSetAll ρ n ⊆ t) :
    Nonempty (AllGuardedButtonPatternWitness (ρ := ρ) (s := t)) := by
  let s := guardedTruthSetAll ρ n
  have hPattern : GuardedButtonPatternAll ρ s := guardedTruthSetAll_pattern (ρ := ρ)
  by_cases hTop : s = Finset.univ
  · have ht : t = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro i
      have hi : i ∈ s := by
        simp [hTop]
      exact hst hi
    subst ht
    refine ⟨AllGuardedButtonPatternWitness.mk α inferInstance id ?_⟩
    intro i
    change HoldsInfAll ρ (guardedButton i) ↔ i ∈ Finset.univ
    have hi : i ∈ s := by
      simp [hTop]
    constructor
    · intro _
      simp
    · intro _
      exact (hPattern i).2 hi
  · simpa [s] using exists_allFunctions_guardedButton_pattern_above
      (ρ := ρ)
      (s := s)
      (t := t)
      (hPart := realizedPartition_eq_pattern_of_guardedPattern_not_top_all
        (ρ := ρ) (s := s) hPattern hTop)
      hst

theorem exists_surjections_guardedTruthSet_above {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} (t : Finset (Fin n))
    (hst : guardedTruthSetSurj ρ n ⊆ t) :
    Nonempty (SurjGuardedButtonPatternWitness (ρ := ρ) (s := t)) := by
  let s := guardedTruthSetSurj ρ n
  have hPattern : GuardedButtonPatternSurj ρ s := guardedTruthSetSurj_pattern (ρ := ρ)
  by_cases hTop : s = Finset.univ
  · have ht : t = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro i
      have hi : i ∈ s := by
        simp [hTop]
      exact hst hi
    subst ht
    refine ⟨SurjGuardedButtonPatternWitness.mk α inferInstance id Function.surjective_id ?_⟩
    intro i
    change HoldsInfSurj ρ (guardedButton i) ↔ i ∈ Finset.univ
    have hi : i ∈ s := by
      simp [hTop]
    constructor
    · intro _
      simp
    · intro _
      exact (hPattern i).2 hi
  · simpa [s] using exists_surjections_guardedButton_pattern_above
      (ρ := ρ)
      (s := s)
      (t := t)
      (hPart := realizedPartition_eq_pattern_of_guardedPattern_not_top_surj
        (ρ := ρ) (s := s) hPattern hTop)
      hst

theorem isPure_guardedButton {n : Nat} (i : Fin n) :
    Equality.IsPure (guardedButton i) := by
  exact And.intro trivial (isPure_crossWiring n)

def guardedLabel {n : Nat} (s : Finset (Fin n)) : EqAssertion :=
  Equality.conjList ((List.finRange n).map fun i =>
    if i ∈ s then guardedButton i else EqAssertion.neg (guardedButton i))

theorem isPure_guardedLabel {n : Nat} (s : Finset (Fin n)) :
    Equality.IsPure (guardedLabel s) := by
  unfold guardedLabel
  apply isPure_conjList
  intro φ hφ
  rcases List.mem_map.mp hφ with ⟨i, _, rfl⟩
  by_cases hi : i ∈ s
  · simpa [hi] using isPure_guardedButton i
  · have hNeg : Equality.IsPure (EqAssertion.neg (guardedButton i)) := by
      change Equality.IsPure (EqAssertion.impl (guardedButton i) EqAssertion.falsum)
      exact And.intro (isPure_guardedButton i) trivial
    simpa [hi] using hNeg

theorem holds_guardedLabel_iff_pattern {admits : Accessibility} {α : Type u}
    (ρ : Valuation α) {n : Nat} (s : Finset (Fin n)) :
    Equality.Holds admits ρ (guardedLabel s) ↔
      ∀ i, Equality.Holds admits ρ (guardedButton i) ↔ i ∈ s := by
  unfold guardedLabel
  rw [Equality.holds_conjList_iff (ρ := ρ)]
  constructor
  · intro h i
    by_cases hi : i ∈ s
    · have hiMem : i ∈ List.finRange n := by
        exact List.mem_finRange i
      have hMem :
          guardedButton i ∈
            (List.finRange n).map (fun j => if j ∈ s then guardedButton j else EqAssertion.neg (guardedButton j)) := by
        exact List.mem_map.mpr (Exists.intro i (And.intro hiMem (by simp [hi])))
      have hClause : Equality.Holds admits ρ (guardedButton i) := h _ hMem
      constructor
      · intro _
        exact hi
      · intro _
        exact hClause
    · have hiMem : i ∈ List.finRange n := by
        exact List.mem_finRange i
      have hMem :
          EqAssertion.neg (guardedButton i) ∈
            (List.finRange n).map (fun j => if j ∈ s then guardedButton j else EqAssertion.neg (guardedButton j)) := by
        exact List.mem_map.mpr (Exists.intro i (And.intro hiMem (by simp [hi])))
      have hClause : Equality.Holds admits ρ (EqAssertion.neg (guardedButton i)) := h _ hMem
      have hNot : ¬ Equality.Holds admits ρ (guardedButton i) := by
        change Equality.Holds admits ρ (EqAssertion.impl (guardedButton i) EqAssertion.falsum) at hClause
        exact hClause
      constructor
      · intro hGuard
        exact False.elim (hNot hGuard)
      · intro hIn
        exact False.elim (hi hIn)
  · intro h φ hφ
    rcases List.mem_map.mp hφ with ⟨i, _, rfl⟩
    by_cases hi : i ∈ s
    · simpa [hi] using (h i).2 hi
    · have hNot : ¬ Equality.Holds admits ρ (guardedButton i) := by
        intro hGuard
        exact hi ((h i).1 hGuard)
      have hNeg : Equality.Holds admits ρ (EqAssertion.neg (guardedButton i)) := by
        change Equality.Holds admits ρ (EqAssertion.impl (guardedButton i) EqAssertion.falsum)
        exact hNot
      simpa [hi] using hNeg

theorem holdsInfAll_guardedLabel_iff {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} (s : Finset (Fin n)) :
    HoldsInfAll ρ (guardedLabel s) ↔ guardedTruthSetAll ρ n = s := by
  have hPure : Equality.IsPure (guardedLabel s) := isPure_guardedLabel s
  rw [holdsInfAll_pure_iff_holds (ρ := ρ) (φ := guardedLabel s) hPure]
  constructor
  · intro hLabel
    apply guardedTruthSetAll_eq_of_pattern (ρ := ρ)
    intro i
    have hPat := (holds_guardedLabel_iff_pattern
      (admits := allAccessibility) (ρ := ρ) (s := s)).mp hLabel i
    simpa [holdsInfAll_pure_iff_holds (ρ := ρ) (φ := guardedButton i) (isPure_guardedButton i)]
      using hPat
  · intro hEq
    have hPattern : GuardedButtonPatternAll ρ s := by
      simpa [hEq] using guardedTruthSetAll_pattern (ρ := ρ) (n := n)
    exact (holds_guardedLabel_iff_pattern
      (admits := allAccessibility) (ρ := ρ) (s := s)).mpr
      (fun i =>
        (holdsInfAll_pure_iff_holds (ρ := ρ) (φ := guardedButton i) (isPure_guardedButton i)).1
          |> fun hToHolds =>
        (holdsInfAll_pure_iff_holds (ρ := ρ) (φ := guardedButton i) (isPure_guardedButton i)).2
          |> fun hToInfAll =>
        by
          constructor
          · intro hHolds
            exact (hPattern i).1 (hToInfAll hHolds)
          · intro hi
            exact hToHolds ((hPattern i).2 hi))

theorem holdsInfSurj_guardedLabel_iff {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} (s : Finset (Fin n)) :
    HoldsInfSurj ρ (guardedLabel s) ↔ guardedTruthSetSurj ρ n = s := by
  have hPure : Equality.IsPure (guardedLabel s) := isPure_guardedLabel s
  rw [holdsInfSurj_pure_iff_holds (ρ := ρ) (φ := guardedLabel s) hPure]
  constructor
  · intro hLabel
    apply guardedTruthSetSurj_eq_of_pattern (ρ := ρ)
    intro i
    have hPat := (holds_guardedLabel_iff_pattern
      (admits := surjectiveAccessibility) (ρ := ρ) (s := s)).mp hLabel i
    simpa [holdsInfSurj_pure_iff_holds (ρ := ρ) (φ := guardedButton i) (isPure_guardedButton i)]
      using hPat
  · intro hEq
    have hPattern : GuardedButtonPatternSurj ρ s := by
      simpa [hEq] using guardedTruthSetSurj_pattern (ρ := ρ) (n := n)
    exact (holds_guardedLabel_iff_pattern
      (admits := surjectiveAccessibility) (ρ := ρ) (s := s)).mpr
      (fun i =>
        (holdsInfSurj_pure_iff_holds (ρ := ρ) (φ := guardedButton i) (isPure_guardedButton i)).1
          |> fun hToHolds =>
        (holdsInfSurj_pure_iff_holds (ρ := ρ) (φ := guardedButton i) (isPure_guardedButton i)).2
          |> fun hToInfSurj =>
        by
          constructor
          · intro hHolds
            exact (hPattern i).1 (hToInfSurj hHolds)
          · intro hi
            exact hToHolds ((hPattern i).2 hi))

def booleanWorlds (n : Nat) : List (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).toList

def guardedLabelList {ι : Type v} (n : Nat) (val : Finset (Fin n) → ι → Prop) (p : ι) :
    List EqAssertion :=
  ((booleanWorlds n).filter fun s => val s p).map guardedLabel

def guardedLabelSubst {ι : Type v} (n : Nat) (val : Finset (Fin n) → ι → Prop) :
    ι → EqAssertion :=
  fun p => Equality.disjList (guardedLabelList n val p)

theorem isPure_guardedLabelSubst {ι : Type v} (n : Nat)
    (val : Finset (Fin n) → ι → Prop) (p : ι) :
    Equality.IsPure (guardedLabelSubst n val p) := by
  unfold guardedLabelSubst guardedLabelList
  apply isPure_disjList
  intro φ hφ
  rcases List.mem_map.mp hφ with ⟨s, _, rfl⟩
  exact isPure_guardedLabel s

theorem holdsInfAll_guardedLabelSubst_iff {ι : Type v} {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} (val : Finset (Fin n) → ι → Prop) (p : ι) :
    HoldsInfAll ρ (guardedLabelSubst n val p) ↔ val (guardedTruthSetAll ρ n) p := by
  have hPure : Equality.IsPure (guardedLabelSubst n val p) := isPure_guardedLabelSubst n val p
  rw [holdsInfAll_pure_iff_holds (ρ := ρ) (φ := guardedLabelSubst n val p) hPure]
  unfold guardedLabelSubst guardedLabelList booleanWorlds
  rw [Equality.holds_disjList_iff (ρ := ρ)]
  constructor
  · rintro ⟨φ, hφMem, hφ⟩
    rcases List.mem_map.mp hφMem with ⟨s, hsMem, rfl⟩
    have hsVal : val s p := by
      simpa using (List.mem_filter.mp hsMem).2
    have hEq : guardedTruthSetAll ρ n = s := by
      exact (holdsInfAll_guardedLabel_iff (ρ := ρ) (s := s)).mp <|
        (holdsInfAll_pure_iff_holds (ρ := ρ) (φ := guardedLabel s) (isPure_guardedLabel s)).2 hφ
    simpa [hEq] using hsVal
  · intro hVal
    have hMem :
        guardedLabel (guardedTruthSetAll ρ n) ∈
          List.map guardedLabel
            (List.filter (fun s => val s p) ((Finset.univ : Finset (Finset (Fin n))).toList)) := by
      apply List.mem_map.mpr
      apply Exists.intro (guardedTruthSetAll ρ n)
      apply And.intro
      · apply List.mem_filter.mpr
        constructor
        · show guardedTruthSetAll ρ n ∈ (Finset.univ : Finset (Finset (Fin n))).toList
          simp
        · simpa using hVal
      · rfl
    have hLabel :
        Holds (fun {α β} => allAccessibility) ρ (guardedLabel (guardedTruthSetAll ρ n)) := by
      have hLabelInf :
          HoldsInfAll ρ (guardedLabel (guardedTruthSetAll ρ n)) :=
        (holdsInfAll_guardedLabel_iff (ρ := ρ) (s := guardedTruthSetAll ρ n)).2 rfl
      exact (holdsInfAll_pure_iff_holds
        (ρ := ρ) (φ := guardedLabel (guardedTruthSetAll ρ n))
        (isPure_guardedLabel (guardedTruthSetAll ρ n))).1 hLabelInf
    exact Exists.intro (guardedLabel (guardedTruthSetAll ρ n)) (And.intro hMem hLabel)

theorem holdsInfSurj_guardedLabelSubst_iff {ι : Type v} {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat} (val : Finset (Fin n) → ι → Prop) (p : ι) :
    HoldsInfSurj ρ (guardedLabelSubst n val p) ↔ val (guardedTruthSetSurj ρ n) p := by
  have hPure : Equality.IsPure (guardedLabelSubst n val p) := isPure_guardedLabelSubst n val p
  rw [holdsInfSurj_pure_iff_holds (ρ := ρ) (φ := guardedLabelSubst n val p) hPure]
  unfold guardedLabelSubst guardedLabelList booleanWorlds
  rw [Equality.holds_disjList_iff (ρ := ρ)]
  constructor
  · rintro ⟨φ, hφMem, hφ⟩
    rcases List.mem_map.mp hφMem with ⟨s, hsMem, rfl⟩
    have hsVal : val s p := by
      simpa using (List.mem_filter.mp hsMem).2
    have hEq : guardedTruthSetSurj ρ n = s := by
      exact (holdsInfSurj_guardedLabel_iff (ρ := ρ) (s := s)).mp <|
        (holdsInfSurj_pure_iff_holds (ρ := ρ) (φ := guardedLabel s) (isPure_guardedLabel s)).2 hφ
    simpa [hEq] using hsVal
  · intro hVal
    have hMem :
        guardedLabel (guardedTruthSetSurj ρ n) ∈
          List.map guardedLabel
            (List.filter (fun s => val s p) ((Finset.univ : Finset (Finset (Fin n))).toList)) := by
      apply List.mem_map.mpr
      apply Exists.intro (guardedTruthSetSurj ρ n)
      apply And.intro
      · apply List.mem_filter.mpr
        constructor
        · show guardedTruthSetSurj ρ n ∈ (Finset.univ : Finset (Finset (Fin n))).toList
          simp
        · simpa using hVal
      · rfl
    have hLabel :
        Holds (fun {α β} => surjectiveAccessibility) ρ (guardedLabel (guardedTruthSetSurj ρ n)) := by
      have hLabelInf :
          HoldsInfSurj ρ (guardedLabel (guardedTruthSetSurj ρ n)) :=
        (holdsInfSurj_guardedLabel_iff (ρ := ρ) (s := guardedTruthSetSurj ρ n)).2 rfl
      exact (holdsInfSurj_pure_iff_holds
        (ρ := ρ) (φ := guardedLabel (guardedTruthSetSurj ρ n))
        (isPure_guardedLabel (guardedTruthSetSurj ρ n))).1 hLabelInf
    exact Exists.intro (guardedLabel (guardedTruthSetSurj ρ n)) (And.intro hMem hLabel)

theorem satisfies_booleanFrameAll_iff_holdsInfAll_translate
    {ι : Type v} {n : Nat} (val : Finset (Fin n) → ι → Prop)
    {α : Type u} [Infinite α] (ρ : Valuation α) (phi : Formula ι) :
    let tau := guardedLabelSubst n val
    let M : Model (Finset (Fin n)) ι := mkModel (BooleanFrames.frame n) val
    satisfies M (guardedTruthSetAll ρ n) phi ↔ HoldsInfAll ρ (PropSubst.translate tau phi) := by
  intro tau M
  induction phi generalizing α ρ with
  | var p =>
      simpa [M] using (holdsInfAll_guardedLabelSubst_iff (ρ := ρ) (n := n) val p).symm
  | bot =>
      rfl
  | imp phi psi ihPhi ihPsi =>
      constructor
      · intro hImp hPhi
        exact (ihPsi (ρ := ρ)).1 (hImp ((ihPhi (ρ := ρ)).2 hPhi))
      · intro hImp hPhi
        exact (ihPsi (ρ := ρ)).2 (hImp ((ihPhi (ρ := ρ)).1 hPhi))
  | conj phi psi ihPhi ihPsi =>
      constructor
      · rintro ⟨hPhi, hPsi⟩
        exact And.intro ((ihPhi (ρ := ρ)).1 hPhi) ((ihPsi (ρ := ρ)).1 hPsi)
      · rintro ⟨hPhi, hPsi⟩
        exact And.intro ((ihPhi (ρ := ρ)).2 hPhi) ((ihPsi (ρ := ρ)).2 hPsi)
  | disj phi psi ihPhi ihPsi =>
      constructor
      · intro h
        rcases h with hPhi | hPsi
        · exact Or.inl ((ihPhi (ρ := ρ)).1 hPhi)
        · exact Or.inr ((ihPsi (ρ := ρ)).1 hPsi)
      · intro h
        rcases h with hPhi | hPsi
        · exact Or.inl ((ihPhi (ρ := ρ)).2 hPhi)
        · exact Or.inr ((ihPsi (ρ := ρ)).2 hPsi)
  | box phi ih =>
      constructor
      · intro hBox β hβ f hf
        have hs :
            guardedTruthSetAll ρ n ⊆ guardedTruthSetAll (fun i => f (ρ i)) n :=
          guardedTruthSetAll_mono (ρ := ρ) (n := n) f
        exact (ih (α := β) (ρ := fun i => f (ρ i))).1 (hBox _ hs)
      · intro hBox t hst
        rcases exists_allFunctions_guardedTruthSet_above (ρ := ρ) (n := n) t hst with ⟨w⟩
        letI : Infinite w.β := w.hβ
        have hEq : guardedTruthSetAll (fun i => w.f (ρ i)) n = t :=
          guardedTruthSetAll_eq_of_pattern (ρ := fun i => w.f (ρ i)) w.pattern
        have hTarget :
            HoldsInfAll (fun i => w.f (ρ i)) (PropSubst.translate tau phi) := by
          exact hBox _ inferInstance w.f trivial
        have hModel :
            satisfies M (guardedTruthSetAll (fun i => w.f (ρ i)) n) phi :=
          (ih (α := w.β) (ρ := fun i => w.f (ρ i))).2 hTarget
        simpa [hEq] using hModel
  | dia phi ih =>
      constructor
      · rintro ⟨t, hst, hModel⟩
        rcases exists_allFunctions_guardedTruthSet_above (ρ := ρ) (n := n) t hst with ⟨w⟩
        letI : Infinite w.β := w.hβ
        refine Exists.intro w.β ?_
        refine Exists.intro w.hβ ?_
        refine Exists.intro w.f ?_
        constructor
        · trivial
        · have hEq : guardedTruthSetAll (fun i => w.f (ρ i)) n = t :=
            guardedTruthSetAll_eq_of_pattern (ρ := fun i => w.f (ρ i)) w.pattern
          have hModel' :
              satisfies M (guardedTruthSetAll (fun i => w.f (ρ i)) n) phi := by
            simpa [hEq] using hModel
          exact (ih (α := w.β) (ρ := fun i => w.f (ρ i))).1 hModel'
      · rintro ⟨β, hβ, f, hf, hPhi⟩
        let t : Finset (Fin n) := guardedTruthSetAll (fun i => f (ρ i)) n
        have hst : guardedTruthSetAll ρ n ⊆ t :=
          guardedTruthSetAll_mono (ρ := ρ) (n := n) f
        refine Exists.intro t ?_
        refine And.intro hst ?_
        exact (ih (α := β) (ρ := fun i => f (ρ i))).2 hPhi

theorem satisfies_booleanFrameSurj_iff_holdsInfSurj_translate
    {ι : Type v} {n : Nat} (val : Finset (Fin n) → ι → Prop)
    {α : Type u} [Infinite α] (ρ : Valuation α) (phi : Formula ι) :
    let tau := guardedLabelSubst n val
    let M : Model (Finset (Fin n)) ι := mkModel (BooleanFrames.frame n) val
    satisfies M (guardedTruthSetSurj ρ n) phi ↔ HoldsInfSurj ρ (PropSubst.translate tau phi) := by
  intro tau M
  induction phi generalizing α ρ with
  | var p =>
      simpa [M] using (holdsInfSurj_guardedLabelSubst_iff (ρ := ρ) (n := n) val p).symm
  | bot =>
      rfl
  | imp phi psi ihPhi ihPsi =>
      constructor
      · intro hImp hPhi
        exact (ihPsi (ρ := ρ)).1 (hImp ((ihPhi (ρ := ρ)).2 hPhi))
      · intro hImp hPhi
        exact (ihPsi (ρ := ρ)).2 (hImp ((ihPhi (ρ := ρ)).1 hPhi))
  | conj phi psi ihPhi ihPsi =>
      constructor
      · rintro ⟨hPhi, hPsi⟩
        exact And.intro ((ihPhi (ρ := ρ)).1 hPhi) ((ihPsi (ρ := ρ)).1 hPsi)
      · rintro ⟨hPhi, hPsi⟩
        exact And.intro ((ihPhi (ρ := ρ)).2 hPhi) ((ihPsi (ρ := ρ)).2 hPsi)
  | disj phi psi ihPhi ihPsi =>
      constructor
      · intro h
        rcases h with hPhi | hPsi
        · exact Or.inl ((ihPhi (ρ := ρ)).1 hPhi)
        · exact Or.inr ((ihPsi (ρ := ρ)).1 hPsi)
      · intro h
        rcases h with hPhi | hPsi
        · exact Or.inl ((ihPhi (ρ := ρ)).2 hPhi)
        · exact Or.inr ((ihPsi (ρ := ρ)).2 hPsi)
  | box phi ih =>
      constructor
      · intro hBox β hβ f hf
        have hs :
            guardedTruthSetSurj ρ n ⊆ guardedTruthSetSurj (fun i => f (ρ i)) n :=
          guardedTruthSetSurj_mono (ρ := ρ) (n := n) f hf
        exact (ih (α := β) (ρ := fun i => f (ρ i))).1 (hBox _ hs)
      · intro hBox t hst
        rcases exists_surjections_guardedTruthSet_above (ρ := ρ) (n := n) t hst with ⟨w⟩
        letI : Infinite w.β := w.hβ
        have hEq : guardedTruthSetSurj (fun i => w.f (ρ i)) n = t :=
          guardedTruthSetSurj_eq_of_pattern (ρ := fun i => w.f (ρ i)) w.pattern
        have hTarget :
            HoldsInfSurj (fun i => w.f (ρ i)) (PropSubst.translate tau phi) := by
          exact hBox _ inferInstance w.f w.hsurj
        have hModel :
            satisfies M (guardedTruthSetSurj (fun i => w.f (ρ i)) n) phi :=
          (ih (α := w.β) (ρ := fun i => w.f (ρ i))).2 hTarget
        simpa [hEq] using hModel
  | dia phi ih =>
      constructor
      · rintro ⟨t, hst, hModel⟩
        rcases exists_surjections_guardedTruthSet_above (ρ := ρ) (n := n) t hst with ⟨w⟩
        letI : Infinite w.β := w.hβ
        refine Exists.intro w.β ?_
        refine Exists.intro w.hβ ?_
        refine Exists.intro w.f ?_
        constructor
        · exact w.hsurj
        · have hEq : guardedTruthSetSurj (fun i => w.f (ρ i)) n = t :=
            guardedTruthSetSurj_eq_of_pattern (ρ := fun i => w.f (ρ i)) w.pattern
          have hModel' :
              satisfies M (guardedTruthSetSurj (fun i => w.f (ρ i)) n) phi := by
            simpa [hEq] using hModel
          exact (ih (α := w.β) (ρ := fun i => w.f (ρ i))).1 hModel'
      · rintro ⟨β, hβ, f, hf, hPhi⟩
        let t : Finset (Fin n) := guardedTruthSetSurj (fun i => f (ρ i)) n
        have hst : guardedTruthSetSurj ρ n ⊆ t :=
          guardedTruthSetSurj_mono (ρ := ρ) (n := n) f hf
        refine Exists.intro t ?_
        refine And.intro hst ?_
        exact (ih (α := β) (ρ := fun i => f (ρ i))).2 hPhi

theorem holdsInfAll_translate_of_booleanFrame_valid
    {ι : Type v} {n : Nat} (val : Finset (Fin n) → ι → Prop)
    {phi : Formula ι} (hValid : (BooleanFrames.frame n).Valid phi)
    {α : Type u} [Infinite α] (ρ : Valuation α) :
    HoldsInfAll ρ (PropSubst.translate (guardedLabelSubst n val) phi) := by
  exact (satisfies_booleanFrameAll_iff_holdsInfAll_translate
    (val := val) (ρ := ρ) phi).1 (hValid val (guardedTruthSetAll ρ n))

theorem holdsInfSurj_translate_of_booleanFrame_valid
    {ι : Type v} {n : Nat} (val : Finset (Fin n) → ι → Prop)
    {phi : Formula ι} (hValid : (BooleanFrames.frame n).Valid phi)
    {α : Type u} [Infinite α] (ρ : Valuation α) :
    HoldsInfSurj ρ (PropSubst.translate (guardedLabelSubst n val) phi) := by
  exact (satisfies_booleanFrameSurj_iff_holdsInfSurj_translate
    (val := val) (ρ := ρ) phi).1 (hValid val (guardedTruthSetSurj ρ n))

theorem holdsInfAll_translate_of_validOnAllFiniteBooleanFrames
    {ι : Type v} {n : Nat} (val : Finset (Fin n) → ι → Prop)
    {phi : Formula ι}
    (hValid : BooleanFrames.ValidOnAllFiniteBooleanFrames phi)
    {α : Type u} [Infinite α] (ρ : Valuation α) :
    HoldsInfAll ρ (PropSubst.translate (guardedLabelSubst n val) phi) :=
  holdsInfAll_translate_of_booleanFrame_valid (n := n) (val := val) (hValid := hValid n) (ρ := ρ)

theorem holdsInfSurj_translate_of_validOnAllFiniteBooleanFrames
    {ι : Type v} {n : Nat} (val : Finset (Fin n) → ι → Prop)
    {phi : Formula ι}
    (hValid : BooleanFrames.ValidOnAllFiniteBooleanFrames phi)
    {α : Type u} [Infinite α] (ρ : Valuation α) :
    HoldsInfSurj ρ (PropSubst.translate (guardedLabelSubst n val) phi) :=
  holdsInfSurj_translate_of_booleanFrame_valid (n := n) (val := val) (hValid := hValid n) (ρ := ρ)

theorem canonical_guardedTruthSetAll_eq {n : Nat} (s : Finset (Fin n)) :
    guardedTruthSetAll
      (infinitePartitionWitnessValuationLift (patternPartition n s)) n = s := by
  exact guardedTruthSetAll_eq_of_pattern
    (ρ := infinitePartitionWitnessValuationLift (patternPartition n s))
    (canonical_guardedButton_pattern_all s)

theorem canonical_guardedTruthSetSurj_eq {n : Nat} (s : Finset (Fin n)) :
    guardedTruthSetSurj
      (infinitePartitionWitnessValuationLift (patternPartition n s)) n = s := by
  exact guardedTruthSetSurj_eq_of_pattern
    (ρ := infinitePartitionWitnessValuationLift (patternPartition n s))
    (canonical_guardedButton_pattern_surj s)

theorem guardedTruthSetAll_eq_empty_of_root_injective {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat}
    (hInj : Function.Injective (fun i : Fin (2 * n) => ρ i.1)) :
    guardedTruthSetAll ρ n = ∅ := by
  ext i
  constructor
  · intro hi
    exact False.elim
      (allFunctions_guardedButton_unpushed_at_root ρ hInj i
        ((mem_guardedTruthSetAll_iff (ρ := ρ)).1 hi))
  · intro hi
    exact False.elim (Finset.notMem_empty i hi)

theorem guardedTruthSetSurj_eq_empty_of_root_injective {α : Type u} [Infinite α]
    (ρ : Valuation α) {n : Nat}
    (hInj : Function.Injective (fun i : Fin (2 * n) => ρ i.1)) :
    guardedTruthSetSurj ρ n = ∅ := by
  ext i
  constructor
  · intro hi
    exact False.elim
      (surjections_guardedButton_unpushed_at_root ρ hInj i
        ((mem_guardedTruthSetSurj_iff (ρ := ρ)).1 hi))
  · intro hi
    exact False.elim (Finset.notMem_empty i hi)

theorem satisfies_booleanFrameAll_empty_iff_holdsInfAll_translate_at_root
    {ι : Type v} {n : Nat} (val : Finset (Fin n) → ι → Prop)
    {α : Type u} [Infinite α] (ρ : Valuation α)
    (hInj : Function.Injective (fun i : Fin (2 * n) => ρ i.1))
    (phi : Formula ι) :
    let M : Model (Finset (Fin n)) ι := mkModel (BooleanFrames.frame n) val
    satisfies M ∅ phi ↔ HoldsInfAll ρ (PropSubst.translate (guardedLabelSubst n val) phi) := by
  intro M
  have hEq : guardedTruthSetAll ρ n = ∅ :=
    guardedTruthSetAll_eq_empty_of_root_injective ρ hInj
  simpa [hEq] using
    (satisfies_booleanFrameAll_iff_holdsInfAll_translate (val := val) (ρ := ρ) phi)

theorem satisfies_booleanFrameSurj_empty_iff_holdsInfSurj_translate_at_root
    {ι : Type v} {n : Nat} (val : Finset (Fin n) → ι → Prop)
    {α : Type u} [Infinite α] (ρ : Valuation α)
    (hInj : Function.Injective (fun i : Fin (2 * n) => ρ i.1))
    (phi : Formula ι) :
    let M : Model (Finset (Fin n)) ι := mkModel (BooleanFrames.frame n) val
    satisfies M ∅ phi ↔ HoldsInfSurj ρ (PropSubst.translate (guardedLabelSubst n val) phi) := by
  intro M
  have hEq : guardedTruthSetSurj ρ n = ∅ :=
    guardedTruthSetSurj_eq_empty_of_root_injective ρ hInj
  simpa [hEq] using
    (satisfies_booleanFrameSurj_iff_holdsInfSurj_translate (val := val) (ρ := ρ) phi)

theorem satisfies_booleanFrameAll_empty_iff_holdsInfAll_translate_at_nat_root
    {ι : Type v} {n : Nat} (val : Finset (Fin n) → ι → Prop) (phi : Formula ι) :
    let M : Model (Finset (Fin n)) ι := mkModel (BooleanFrames.frame n) val
    satisfies M ∅ phi ↔
      HoldsInfAll (fun k : Nat => k) (PropSubst.translate (guardedLabelSubst n val) phi) := by
  exact satisfies_booleanFrameAll_empty_iff_holdsInfAll_translate_at_root
    (val := val) (ρ := fun k : Nat => k) (hInj := prefixInjective_nat (2 * n)) phi

theorem satisfies_booleanFrameSurj_empty_iff_holdsInfSurj_translate_at_nat_root
    {ι : Type v} {n : Nat} (val : Finset (Fin n) → ι → Prop) (phi : Formula ι) :
    let M : Model (Finset (Fin n)) ι := mkModel (BooleanFrames.frame n) val
    satisfies M ∅ phi ↔
      HoldsInfSurj (fun k : Nat => k) (PropSubst.translate (guardedLabelSubst n val) phi) := by
  exact satisfies_booleanFrameSurj_empty_iff_holdsInfSurj_translate_at_root
    (val := val) (ρ := fun k : Nat => k) (hInj := prefixInjective_nat (2 * n)) phi

theorem booleanFrame_validAtBottom_iff_holdsInfAll_guardedLabelSubst_at_nat_root
    {ι : Type v} {n : Nat} {phi : Formula ι} :
    BooleanFrames.ValidAtBottom n phi ↔
      ∀ val, HoldsInfAll (fun k : Nat => k)
        (PropSubst.translate (guardedLabelSubst n val) phi) := by
  constructor
  · intro hBottom val
    exact (satisfies_booleanFrameAll_empty_iff_holdsInfAll_translate_at_nat_root
      (n := n) (val := val) phi).1 (hBottom val)
  · intro hRoot val
    exact (satisfies_booleanFrameAll_empty_iff_holdsInfAll_translate_at_nat_root
      (n := n) (val := val) phi).2 (hRoot val)

theorem booleanFrame_validAtBottom_iff_holdsInfSurj_guardedLabelSubst_at_nat_root
    {ι : Type v} {n : Nat} {phi : Formula ι} :
    BooleanFrames.ValidAtBottom n phi ↔
      ∀ val, HoldsInfSurj (fun k : Nat => k)
        (PropSubst.translate (guardedLabelSubst n val) phi) := by
  constructor
  · intro hBottom val
    exact (satisfies_booleanFrameSurj_empty_iff_holdsInfSurj_translate_at_nat_root
      (n := n) (val := val) phi).1 (hBottom val)
  · intro hRoot val
    exact (satisfies_booleanFrameSurj_empty_iff_holdsInfSurj_translate_at_nat_root
      (n := n) (val := val) phi).2 (hRoot val)

theorem booleanFrame_valid_iff_holdsInfAll_guardedLabelSubst_at_nat_root
    {ι : Type v} {n : Nat} {phi : Formula ι} :
    (BooleanFrames.frame n).Valid phi ↔
      ∀ val, HoldsInfAll (fun k : Nat => k)
        (PropSubst.translate (guardedLabelSubst n val) phi) := by
  rw [BooleanFrames.valid_iff_validAtBottom]
  exact booleanFrame_validAtBottom_iff_holdsInfAll_guardedLabelSubst_at_nat_root

theorem booleanFrame_valid_iff_holdsInfSurj_guardedLabelSubst_at_nat_root
    {ι : Type v} {n : Nat} {phi : Formula ι} :
    (BooleanFrames.frame n).Valid phi ↔
      ∀ val, HoldsInfSurj (fun k : Nat => k)
        (PropSubst.translate (guardedLabelSubst n val) phi) := by
  rw [BooleanFrames.valid_iff_validAtBottom]
  exact booleanFrame_validAtBottom_iff_holdsInfSurj_guardedLabelSubst_at_nat_root

def AllGuardedLabelSubstValid {ι : Type v} (n : Nat) (phi : Formula ι) : Prop :=
  ∀ (val : Finset (Fin n) → ι → Prop) (α : Type u) (_ : Infinite α) (ρ : Valuation α),
      HoldsInfAll ρ (PropSubst.translate (guardedLabelSubst n val) phi)

def SurjGuardedLabelSubstValid {ι : Type v} (n : Nat) (phi : Formula ι) : Prop :=
  ∀ (val : Finset (Fin n) → ι → Prop) (α : Type u) (_ : Infinite α) (ρ : Valuation α),
      HoldsInfSurj ρ (PropSubst.translate (guardedLabelSubst n val) phi)

theorem booleanFrame_valid_iff_holdsInfAll_guardedLabelSubst
    {ι : Type v} {n : Nat} {phi : Formula ι} :
    (BooleanFrames.frame n).Valid phi ↔ AllGuardedLabelSubstValid n phi := by
  constructor
  · intro hValid val α hα ρ
    letI : Infinite α := hα
    exact holdsInfAll_translate_of_booleanFrame_valid (n := n) (val := val) (hValid := hValid) (ρ := ρ)
  · intro hValid val s
    let ρ : Valuation (ULift (InfinitePartitionWitnessWorld (patternPartition n s))) :=
      infinitePartitionWitnessValuationLift (patternPartition n s)
    have hTransfer :
        HoldsInfAll ρ (PropSubst.translate (guardedLabelSubst n val) phi) :=
      hValid val _ inferInstance ρ
    have hSat :
        satisfies (mkModel (BooleanFrames.frame n) val) (guardedTruthSetAll ρ n) phi :=
      (satisfies_booleanFrameAll_iff_holdsInfAll_translate (val := val) (ρ := ρ) phi).2 hTransfer
    have hEq : guardedTruthSetAll ρ n = s := by
      simpa [ρ] using (canonical_guardedTruthSetAll_eq (n := n) s)
    simpa [hEq] using hSat

theorem booleanFrame_valid_iff_holdsInfSurj_guardedLabelSubst
    {ι : Type v} {n : Nat} {phi : Formula ι} :
    (BooleanFrames.frame n).Valid phi ↔ SurjGuardedLabelSubstValid n phi := by
  constructor
  · intro hValid val α hα ρ
    letI : Infinite α := hα
    exact holdsInfSurj_translate_of_booleanFrame_valid (n := n) (val := val) (hValid := hValid) (ρ := ρ)
  · intro hValid val s
    let ρ : Valuation (ULift (InfinitePartitionWitnessWorld (patternPartition n s))) :=
      infinitePartitionWitnessValuationLift (patternPartition n s)
    have hTransfer :
        HoldsInfSurj ρ (PropSubst.translate (guardedLabelSubst n val) phi) :=
      hValid val _ inferInstance ρ
    have hSat :
        satisfies (mkModel (BooleanFrames.frame n) val) (guardedTruthSetSurj ρ n) phi :=
      (satisfies_booleanFrameSurj_iff_holdsInfSurj_translate (val := val) (ρ := ρ) phi).2 hTransfer
    have hEq : guardedTruthSetSurj ρ n = s := by
      simpa [ρ] using (canonical_guardedTruthSetSurj_eq (n := n) s)
    simpa [hEq] using hSat

theorem validOnAllFiniteBooleanFrames_iff_holdsInfAll_guardedLabelSubst
    {ι : Type v} {phi : Formula ι} :
    BooleanFrames.ValidOnAllFiniteBooleanFrames phi ↔
      ∀ n, AllGuardedLabelSubstValid n phi := by
  constructor
  · intro hValid n
    exact (booleanFrame_valid_iff_holdsInfAll_guardedLabelSubst
      (n := n) (phi := phi)).1 (hValid n)
  · intro hValid n
    exact (booleanFrame_valid_iff_holdsInfAll_guardedLabelSubst
      (n := n) (phi := phi)).2 (hValid n)

theorem validOnAllFiniteBooleanFrames_iff_holdsInfSurj_guardedLabelSubst
    {ι : Type v} {phi : Formula ι} :
    BooleanFrames.ValidOnAllFiniteBooleanFrames phi ↔
      ∀ n, SurjGuardedLabelSubstValid n phi := by
  constructor
  · intro hValid n
    exact (booleanFrame_valid_iff_holdsInfSurj_guardedLabelSubst
      (n := n) (phi := phi)).1 (hValid n)
  · intro hValid n
    exact (booleanFrame_valid_iff_holdsInfSurj_guardedLabelSubst
      (n := n) (phi := phi)).2 (hValid n)

theorem validOnAllFiniteBooleanFrames_iff_holdsInfAll_guardedLabelSubst_at_nat_root
    {ι : Type v} {phi : Formula ι} :
    BooleanFrames.ValidOnAllFiniteBooleanFrames phi ↔
      ∀ n val, HoldsInfAll (fun k : Nat => k)
        (PropSubst.translate (guardedLabelSubst n val) phi) := by
  constructor
  · intro hValid n
    exact (booleanFrame_valid_iff_holdsInfAll_guardedLabelSubst_at_nat_root
      (n := n) (phi := phi)).1 (hValid n)
  · intro hValid n
    exact (booleanFrame_valid_iff_holdsInfAll_guardedLabelSubst_at_nat_root
      (n := n) (phi := phi)).2 (hValid n)

theorem validOnAllFiniteBooleanFrames_iff_holdsInfSurj_guardedLabelSubst_at_nat_root
    {ι : Type v} {phi : Formula ι} :
    BooleanFrames.ValidOnAllFiniteBooleanFrames phi ↔
      ∀ n val, HoldsInfSurj (fun k : Nat => k)
        (PropSubst.translate (guardedLabelSubst n val) phi) := by
  constructor
  · intro hValid n
    exact (booleanFrame_valid_iff_holdsInfSurj_guardedLabelSubst_at_nat_root
      (n := n) (phi := phi)).1 (hValid n)
  · intro hValid n
    exact (booleanFrame_valid_iff_holdsInfSurj_guardedLabelSubst_at_nat_root
      (n := n) (phi := phi)).2 (hValid n)

end

end Buttons

end HeytingLean.ModalCategorySets.Framework
