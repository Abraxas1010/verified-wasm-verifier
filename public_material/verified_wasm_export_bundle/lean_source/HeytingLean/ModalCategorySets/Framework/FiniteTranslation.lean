import HeytingLean.ModalCategorySets.Framework.EqualityMorphismBridge
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.Nodup
import Mathlib.Data.Setoid.Partition
import Mathlib.Tactic

namespace HeytingLean.ModalCategorySets.Framework.Equality

open scoped Classical

universe u

@[simp] theorem holds_conjList_iff {admits : Accessibility} {α : Type u} (ρ : Valuation α)
    (φs : List EqAssertion) :
    Holds admits ρ (conjList φs) ↔ ∀ φ, φ ∈ φs → Holds admits ρ φ := by
  induction φs with
  | nil =>
      constructor
      · intro _ φ hφ
        cases hφ
      · intro _ hFalse
        exact False.elim hFalse
  | cons φ φs ih =>
      constructor
      · intro h ψ hψ
        rcases h with ⟨hφ, htail⟩
        rw [List.mem_cons] at hψ
        rcases hψ with hψ | hψ
        · cases hψ
          exact hφ
        · exact (ih.mp htail) ψ hψ
      · intro h
        constructor
        · exact h φ List.mem_cons_self
        · exact ih.mpr (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))

@[simp] theorem holds_disjList_iff {admits : Accessibility} {α : Type u} (ρ : Valuation α)
    (φs : List EqAssertion) :
    Holds admits ρ (disjList φs) ↔ ∃ φ, φ ∈ φs ∧ Holds admits ρ φ := by
  induction φs with
  | nil =>
      constructor
      · intro h
        cases h
      · intro h
        rcases h with ⟨φ, hφ, _⟩
        cases hφ
  | cons φ φs ih =>
      constructor
      · intro h
        rcases h with h | h
        · exact Exists.intro φ (And.intro List.mem_cons_self h)
        · rcases ih.mp h with ⟨ψ, hψ, hholds⟩
          exact Exists.intro ψ (And.intro (List.mem_cons_of_mem _ hψ) hholds)
      · intro h
        rcases h with ⟨ψ, hψ, hholds⟩
        rw [List.mem_cons] at hψ
        rcases hψ with hψ | hψ
        · cases hψ
          exact Or.inl hholds
        · exact Or.inr (ih.mpr (Exists.intro ψ (And.intro hψ hholds)))

theorem holds_eqPairsFormula_iff {admits : Accessibility} {α : Type u} (ρ : Valuation α)
    (pairs : List (Var × Var)) :
    Holds admits ρ (eqPairsFormula pairs) ↔ ∀ p, p ∈ pairs → ρ p.1 = ρ p.2 := by
  constructor
  · intro h p hp
    have hmem : EqAssertion.atomEq p.1 p.2 ∈ pairs.map (fun q => EqAssertion.atomEq q.1 q.2) := by
      exact List.mem_map.mpr (Exists.intro p (And.intro hp rfl))
    exact (holds_conjList_iff (ρ := ρ) (φs := pairs.map (fun q => .atomEq q.1 q.2))).1
      (by simpa [eqPairsFormula] using h)
      (.atomEq p.1 p.2) hmem
  · intro h
    refine (holds_conjList_iff (ρ := ρ) (φs := pairs.map (fun q => .atomEq q.1 q.2))).2 ?_
    intro φ hφ
    rcases List.mem_map.1 hφ with ⟨p, hp, rfl⟩
    exact h p hp

theorem holds_neqPairsFormula_iff {admits : Accessibility} {α : Type u} (ρ : Valuation α)
    (pairs : List (Var × Var)) :
    Holds admits ρ (neqPairsFormula pairs) ↔ ∀ p, p ∈ pairs → ρ p.1 ≠ ρ p.2 := by
  constructor
  · intro h p hp
    have hmem :
        EqAssertion.neg (.atomEq p.1 p.2) ∈
          pairs.map (fun q => EqAssertion.neg (.atomEq q.1 q.2)) := by
      exact List.mem_map.mpr (Exists.intro p (And.intro hp rfl))
    have h' :=
      (holds_conjList_iff (ρ := ρ)
        (φs := pairs.map (fun q => EqAssertion.neg (.atomEq q.1 q.2)))).1
        (by simpa [neqPairsFormula] using h)
        (EqAssertion.neg (.atomEq p.1 p.2)) hmem
    exact (holds_neg_atomEq_iff (admits := admits) (ρ := ρ) p.1 p.2).mp h'
  · intro h
    refine (holds_conjList_iff (ρ := ρ)
      (φs := pairs.map (fun q => EqAssertion.neg (.atomEq q.1 q.2)))).2 ?_
    intro φ hφ
    rcases List.mem_map.1 hφ with ⟨p, hp, rfl⟩
    exact (holds_neg_atomEq_iff (admits := admits) (ρ := ρ) p.1 p.2).mpr (h p hp)

theorem holds_pairwiseDistinct_iff_pairwise {admits : Accessibility} {α : Type u}
    (ρ : Valuation α) (vars : List Var) :
    Holds admits ρ (pairwiseDistinct vars) ↔ vars.Pairwise (fun x y => ρ x ≠ ρ y) := by
  induction vars with
  | nil =>
      constructor
      · intro _
        exact List.Pairwise.nil
      · intro _
        change Holds admits ρ (conjList [])
        intro hFalse
        exact False.elim hFalse
  | cons x xs ih =>
      constructor
      · intro h
        unfold pairwiseDistinct at h
        unfold allPairs at h
        have hAll :=
          (holds_neqPairsFormula_iff (ρ := ρ)
            (pairs := xs.map (fun y => Prod.mk x y) ++ allPairs xs)).mp h
        refine List.pairwise_cons.2 ?_
        constructor
        · intro a ha
          exact hAll (Prod.mk x a)
            (List.mem_append.2 <| Or.inl <|
              List.mem_map.2 (Exists.intro a (And.intro ha rfl)))
        · apply ih.mp
          refine (holds_neqPairsFormula_iff (ρ := ρ) (pairs := allPairs xs)).mpr ?_
          intro p hp
          exact hAll p (List.mem_append.2 <| Or.inr hp)
      · intro h
        have hx : ∀ a, a ∈ xs → ρ x ≠ ρ a := (List.pairwise_cons.1 h).1
        have hxs : xs.Pairwise (fun a b => ρ a ≠ ρ b) := (List.pairwise_cons.1 h).2
        have hneq : Holds admits ρ (neqPairsFormula (xs.map (fun y => Prod.mk x y) ++ allPairs xs)) := by
          refine (holds_neqPairsFormula_iff (ρ := ρ)
          (pairs := xs.map (fun y => Prod.mk x y) ++ allPairs xs)).mpr ?_
          intro p hp
          rcases List.mem_append.1 hp with hp | hp
          · rcases List.mem_map.1 hp with ⟨a, ha, hpEq⟩
            cases hpEq
            exact hx a ha
          · have htail := (holds_neqPairsFormula_iff (ρ := ρ) (pairs := allPairs xs)).mp
              (ih.mpr hxs)
            exact htail p hp
        unfold pairwiseDistinct
        unfold allPairs
        exact hneq

theorem holds_eqDisjFormula_iff {admits : Accessibility} {α : Type u} (ρ : Valuation α)
    (pairs : List (Var × Var)) :
    Holds admits ρ (disjList (pairs.map (fun p => EqAssertion.atomEq p.1 p.2))) ↔
      ∃ p, p ∈ pairs ∧ ρ p.1 = ρ p.2 := by
  constructor
  · intro h
    rcases (holds_disjList_iff (ρ := ρ) (φs := pairs.map (fun p => EqAssertion.atomEq p.1 p.2))).mp h with
      ⟨φ, hφ, hholds⟩
    rcases List.mem_map.1 hφ with ⟨p, hp, rfl⟩
    exact Exists.intro p (And.intro hp hholds)
  · intro h
    rcases h with ⟨p, hp, hEq⟩
    refine (holds_disjList_iff (ρ := ρ)
      (φs := pairs.map (fun q => EqAssertion.atomEq q.1 q.2))).mpr ?_
    exact Exists.intro (EqAssertion.atomEq p.1 p.2)
      (And.intro (List.mem_map.2 (Exists.intro p (And.intro hp rfl))) hEq)

theorem holds_someEqual_iff_not_pairwise {admits : Accessibility} {α : Type u}
    (ρ : Valuation α) (vars : List Var) :
    Holds admits ρ (disjList ((allPairs vars).map (fun p => EqAssertion.atomEq p.1 p.2))) ↔
      ¬ vars.Pairwise (fun x y => ρ x ≠ ρ y) := by
  constructor
  · intro h hPair
    rcases (holds_eqDisjFormula_iff (admits := admits) (ρ := ρ) (pairs := allPairs vars)).mp h with
      ⟨p, hp, hEq⟩
    have hNeq :=
      (holds_neqPairsFormula_iff (admits := admits) (ρ := ρ) (pairs := allPairs vars)).mp
        ((holds_pairwiseDistinct_iff_pairwise (admits := admits) (ρ := ρ) (vars := vars)).mpr hPair)
        p hp
    exact hNeq hEq
  · intro hNot
    by_cases hEq : ∃ p, p ∈ allPairs vars ∧ ρ p.1 = ρ p.2
    · exact (holds_eqDisjFormula_iff (admits := admits) (ρ := ρ) (pairs := allPairs vars)).mpr hEq
    · apply False.elim
      apply hNot
      exact (holds_pairwiseDistinct_iff_pairwise (admits := admits) (ρ := ρ) (vars := vars)).mp <|
        (holds_neqPairsFormula_iff (admits := admits) (ρ := ρ) (pairs := allPairs vars)).mpr (by
          intro p hp hEq'
          exact hEq (Exists.intro p (And.intro hp hEq')))

theorem range_pairwise_iff_injective {α : Type u} (ρ : Valuation α) (n : Nat) :
    (List.range n).Pairwise (fun x y => ρ x ≠ ρ y) ↔
      Function.Injective (fun i : Fin n => ρ i.1) := by
  constructor
  · intro h i j hEq
    by_cases hVal : i.1 = j.1
    · exact Fin.ext hVal
    · rcases lt_or_gt_of_ne hVal with hij | hji
      · have hNeq := (List.pairwise_iff_getElem.mp h) i.1 j.1
            (show i.1 < (List.range n).length by
              rw [List.length_range]
              exact i.2)
            (show j.1 < (List.range n).length by
              rw [List.length_range]
              exact j.2) hij
        have hEq' : ρ (List.range n)[i.1] = ρ (List.range n)[j.1] := by
          simpa using hEq
        exact False.elim (hNeq hEq')
      · have hNeq := (List.pairwise_iff_getElem.mp h) j.1 i.1
            (show j.1 < (List.range n).length by
              rw [List.length_range]
              exact j.2)
            (show i.1 < (List.range n).length by
              rw [List.length_range]
              exact i.2) hji
        have hEq' : ρ (List.range n)[j.1] = ρ (List.range n)[i.1] := by
          simpa using hEq.symm
        exact False.elim (hNeq hEq')
  · intro hInj
    refine List.pairwise_iff_getElem.mpr ?_
    intro i j hi hj hij hEq
    have hi' : i < n := by simpa [List.length_range] using hi
    have hj' : j < n := by simpa [List.length_range] using hj
    have hEq' : ρ i = ρ j := by simpa using hEq
    have hFinEq : (Fin.mk i hi' : Fin n) = Fin.mk j hj' := hInj hEq'
    exact (Nat.ne_of_lt hij) (congrArg Fin.val hFinEq)

theorem holds_pairwiseDistinct_range_iff_injective {admits : Accessibility} {α : Type u}
    (ρ : Valuation α) (n : Nat) :
    Holds admits ρ (pairwiseDistinct (List.range n)) ↔
      Function.Injective (fun i : Fin n => ρ i.1) := by
  rw [holds_pairwiseDistinct_iff_pairwise]
  exact range_pairwise_iff_injective ρ n

/-- Bind a finite tuple of witnesses on top of an existing valuation. -/
def bindTuple {α : Type u} (ρ : Valuation α) {n : Nat} (xs : Fin n → α) : Valuation α :=
  fun v => if h : v < n then xs (Fin.mk v h) else ρ (v - n)

@[simp] theorem bindTuple_lt {α : Type u} (ρ : Valuation α) {n v : Nat}
    (xs : Fin n → α) (h : v < n) :
    bindTuple ρ xs v = xs (Fin.mk v h) := by
  unfold bindTuple
  split_ifs with h'
  · rfl
  · exact False.elim (h' h)

@[simp] theorem bindTuple_ge {α : Type u} (ρ : Valuation α) {n v : Nat}
    (xs : Fin n → α) (h : n ≤ v) :
    bindTuple ρ xs v = ρ (v - n) := by
  unfold bindTuple
  split_ifs with h'
  · exact False.elim ((Nat.not_lt.mpr h) h')
  · rfl

@[simp] theorem bindTuple_empty {α : Type u} (ρ : Valuation α) :
    bindTuple ρ (Fin.elim0 : Fin 0 → α) = ρ := by
  funext v
  exact bindTuple_ge ρ (Fin.elim0 : Fin 0 → α) (Nat.zero_le v)

/-- Add one older witness at the far end of a finite tuple. -/
def snocTuple {α : Type u} {n : Nat} (xs : Fin n → α) (a : α) : Fin (n + 1) → α :=
  Fin.snoc xs a

/-- Drop the oldest witness from a nonempty tuple. -/
def initTuple {α : Type u} {n : Nat} (xs : Fin (n + 1) → α) : Fin n → α :=
  fun i => xs i.castSucc

@[simp] theorem initTuple_snoc {α : Type u} {n : Nat} (xs : Fin n → α) (a : α) :
    initTuple (snocTuple xs a) = xs := by
  funext i
  unfold initTuple snocTuple
  simp

@[simp] theorem snocTuple_last {α : Type u} {n : Nat} (xs : Fin n → α) (a : α) :
    snocTuple xs a (Fin.last n) = a := by
  simp [snocTuple]

@[simp] theorem snocTuple_init_last {α : Type u} {n : Nat} (xs : Fin (n + 1) → α) :
    snocTuple (initTuple xs) (xs (Fin.last n)) = xs := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · unfold initTuple snocTuple
    simp
  · simp [snocTuple]

theorem bindTuple_snoc {α : Type u} (ρ : Valuation α) {n : Nat}
    (xs : Fin n → α) (a : α) :
    bindTuple ρ (snocTuple xs a) = bindTuple (extend ρ a) xs := by
  funext v
  by_cases hv : v < n
  · have hv' : v < n + 1 := Nat.lt_succ_of_lt hv
    rw [bindTuple_lt (ρ := ρ) (xs := snocTuple xs a) hv']
    rw [bindTuple_lt (ρ := extend ρ a) (xs := xs) hv]
    have hcast : (Fin.mk v hv).castSucc = Fin.mk v hv' := by
      ext
      rfl
    rw [← hcast]
    simpa [snocTuple] using
      (Fin.snoc_castSucc (α := fun _ : Fin (n + 1) => α)
        (p := xs) (x := a) (i := Fin.mk v hv))
  · have hnv : n ≤ v := Nat.not_lt.mp hv
    by_cases hEq : v = n
    · subst v
      rw [bindTuple_lt (ρ := ρ) (xs := snocTuple xs a) (Nat.lt_succ_self n)]
      rw [bindTuple_ge (ρ := extend ρ a) (xs := xs) (le_rfl : n ≤ n)]
      have hlast : (Fin.mk n (Nat.lt_succ_self n)) = Fin.last n := by
        ext
        rfl
      rw [hlast]
      simp [snocTuple]
    · have hlt : n < v := lt_of_le_of_ne hnv (by
        intro h
        exact hEq h.symm)
      have hv' : n + 1 ≤ v := Nat.succ_le_of_lt hlt
      rw [bindTuple_ge (ρ := ρ) (xs := snocTuple xs a) hv']
      rw [bindTuple_ge (ρ := extend ρ a) (xs := xs) hnv]
      have hsub : v - n = (v - (n + 1)) + 1 := by
        rw [Nat.sub_eq_iff_eq_add hnv]
        omega
      rw [hsub]
      rw [Nat.add_comm]
      simp [extend]

theorem holds_existsN_iff {admits : Accessibility} {α : Type u} (ρ : Valuation α)
    (n : Nat) (φ : EqAssertion) :
    Holds admits ρ (existsN n φ) ↔ Exists (fun xs : Fin n → α => Holds admits (bindTuple ρ xs) φ) := by
  induction n generalizing ρ with
  | zero =>
      constructor
      · intro h
        refine Exists.intro (Fin.elim0 : Fin 0 → α) ?_
        simpa [existsN] using h
      · rintro ⟨xs, h⟩
        simpa [existsN] using h
  | succ n ih =>
      constructor
      · intro h
        rcases h with ⟨a, ha⟩
        rcases (ih (ρ := extend ρ a)).mp ha with ⟨xs, hxs⟩
        refine Exists.intro (snocTuple xs a) ?_
        simpa using (bindTuple_snoc (ρ := ρ) (xs := xs) (a := a) ▸ hxs)
      · rintro ⟨xs, hxs⟩
        refine Exists.intro (xs (Fin.last n)) ?_
        have hSnoc : Holds admits (bindTuple ρ (snocTuple (initTuple xs) (xs (Fin.last n)))) φ := by
          simpa using (snocTuple_init_last xs ▸ hxs)
        have hInit : Holds admits (bindTuple (extend ρ (xs (Fin.last n))) (initTuple xs)) φ := by
          simpa using ((bindTuple_snoc (ρ := ρ) (xs := initTuple xs)
            (a := xs (Fin.last n))).symm ▸ hSnoc)
        exact (ih (ρ := extend ρ (xs (Fin.last n)))).mpr (Exists.intro (initTuple xs) hInit)

theorem holds_forallN_iff {admits : Accessibility} {α : Type u} (ρ : Valuation α)
    (n : Nat) (φ : EqAssertion) :
    Holds admits ρ (forallN n φ) ↔ ((xs : Fin n → α) → Holds admits (bindTuple ρ xs) φ) := by
  induction n generalizing ρ with
  | zero =>
      constructor
      · intro h xs
        simpa [forallN] using h
      · intro h
        simpa [forallN] using h (Fin.elim0 : Fin 0 → α)
  | succ n ih =>
      constructor
      · intro h xs
        have hx : Holds admits (extend ρ (xs (Fin.last n))) (forallN n φ) := by
          simpa [forallN] using h (xs (Fin.last n))
        have hTail := (ih (ρ := extend ρ (xs (Fin.last n)))).mp hx (initTuple xs)
        simpa using ((snocTuple_init_last xs).symm ▸ (bindTuple_snoc (ρ := ρ)
          (xs := initTuple xs) (a := xs (Fin.last n)) ▸ hTail))
      · intro h a
        exact (ih (ρ := extend ρ a)).mpr <| by
          intro xs
          simpa using ((bindTuple_snoc (ρ := ρ) (xs := xs) (a := a)).symm ▸ h (snocTuple xs a))

theorem holds_someEqual_range_iff_not_injective {admits : Accessibility} {α : Type u}
    (ρ : Valuation α) (n : Nat) (xs : Fin n → α) :
    Holds admits (bindTuple ρ xs)
      (disjList ((allPairs (List.range n)).map (fun p => EqAssertion.atomEq p.1 p.2))) ↔
      ¬ Function.Injective xs := by
  have hPair :
      Holds admits (bindTuple ρ xs)
        (disjList ((allPairs (List.range n)).map (fun p => EqAssertion.atomEq p.1 p.2))) ↔
        ¬ (List.range n).Pairwise (fun x y => bindTuple ρ xs x ≠ bindTuple ρ xs y) :=
    holds_someEqual_iff_not_pairwise (admits := admits) (ρ := bindTuple ρ xs) (vars := List.range n)
  rw [hPair]
  exact not_congr (by
    simpa [bindTuple] using
      (range_pairwise_iff_injective (ρ := bindTuple ρ xs) (n := n)))

theorem holds_atLeastCardinality_iff {admits : Accessibility} {α : Type u} (ρ : Valuation α)
    (n : Nat) :
    Holds admits ρ (atLeastCardinality n) ↔ Exists (fun xs : Fin n → α => Function.Injective xs) := by
  rw [atLeastCardinality]
  rw [holds_existsN_iff]
  constructor
  · rintro ⟨xs, hxs⟩
    have hInj :
        Function.Injective (fun i : Fin n => bindTuple ρ xs i.1) :=
      (holds_pairwiseDistinct_range_iff_injective (admits := admits)
        (ρ := bindTuple ρ xs) (n := n)).mp hxs
    refine Exists.intro xs ?_
    simpa [bindTuple] using hInj
  · rintro ⟨xs, hxs⟩
    have hInj :
        Function.Injective (fun i : Fin n => bindTuple ρ xs i.1) := by
      simpa [bindTuple] using hxs
    exact Exists.intro xs ((holds_pairwiseDistinct_range_iff_injective (admits := admits)
      (ρ := bindTuple ρ xs) (n := n)).mpr hInj)

theorem holds_atMostCardinality_iff {admits : Accessibility} {α : Type u} (ρ : Valuation α)
    (n : Nat) :
    Holds admits ρ (atMostCardinality n) ↔
      ((xs : Fin (n + 1) → α) → ¬ Function.Injective xs) := by
  rw [atMostCardinality]
  rw [holds_forallN_iff]
  constructor
  · intro h xs
    exact (holds_someEqual_range_iff_not_injective (admits := admits)
      (ρ := ρ) (n := n + 1) (xs := xs)).mp (h xs)
  · intro h xs
    exact (holds_someEqual_range_iff_not_injective (admits := admits)
      (ρ := ρ) (n := n + 1) (xs := xs)).mpr (h xs)

theorem holds_exactCardinality_iff {admits : Accessibility} {α : Type u} (ρ : Valuation α)
    (n : Nat) :
    Holds admits ρ (exactCardinality n) ↔
      (Exists (fun xs : Fin n → α => Function.Injective xs)) ∧
      (((ys : Fin (n + 1) → α) → ¬ Function.Injective ys)) := by
  rw [exactCardinality]
  constructor
  · intro h
    exact And.intro
      ((holds_atLeastCardinality_iff (admits := admits) (ρ := ρ) n).mp h.1)
      ((holds_atMostCardinality_iff (admits := admits) (ρ := ρ) n).mp h.2)
  · rintro ⟨hAtLeast, hAtMost⟩
    exact And.intro
      ((holds_atLeastCardinality_iff (admits := admits) (ρ := ρ) n).mpr hAtLeast)
      ((holds_atMostCardinality_iff (admits := admits) (ρ := ρ) n).mpr hAtMost)

noncomputable def injectFromFinInto {α : Type u} [Fintype α] {n : Nat}
    (h : n ≤ Fintype.card α) : Fin n → α :=
  fun i => (Fintype.equivFin α).symm (Fin.castLE h i)

theorem injective_injectFromFinInto {α : Type u} [Fintype α] {n : Nat}
    (h : n ≤ Fintype.card α) :
    Function.Injective (injectFromFinInto (α := α) h) := by
  intro i j hij
  apply Fin.castLE_injective h
  simpa [injectFromFinInto] using congrArg (Fintype.equivFin α) hij

theorem holds_atLeastCardinality_iff_fintype_card_ge {admits : Accessibility} {α : Type u}
    [Fintype α] (ρ : Valuation α) (n : Nat) :
    Holds admits ρ (atLeastCardinality n) ↔ n ≤ Fintype.card α := by
  rw [holds_atLeastCardinality_iff]
  constructor
  · rintro ⟨xs, hxs⟩
    simpa using Fintype.card_le_of_injective xs hxs
  · intro h
    exact Exists.intro (injectFromFinInto (α := α) h) (injective_injectFromFinInto (α := α) h)

theorem holds_atMostCardinality_iff_fintype_card_le {admits : Accessibility} {α : Type u}
    [Fintype α] (ρ : Valuation α) (n : Nat) :
    Holds admits ρ (atMostCardinality n) ↔ Fintype.card α ≤ n := by
  rw [holds_atMostCardinality_iff]
  constructor
  · intro h
    by_contra hlt
    have hle : n + 1 ≤ Fintype.card α := by omega
    exact h (injectFromFinInto (α := α) hle) (injective_injectFromFinInto (α := α) hle)
  · intro h xs hxs
    have hcard : Fintype.card (Fin (n + 1)) ≤ Fintype.card α :=
      Fintype.card_le_of_injective xs hxs
    have : n + 1 ≤ Fintype.card α := by simpa using hcard
    omega

theorem holds_exactCardinality_iff_fintype_card_eq {admits : Accessibility} {α : Type u}
    [Fintype α] (ρ : Valuation α) (n : Nat) :
    Holds admits ρ (exactCardinality n) ↔ Fintype.card α = n := by
  rw [exactCardinality]
  constructor
  · intro h
    rcases h with ⟨hAtLeast, hAtMost⟩
    exact le_antisymm
      ((holds_atMostCardinality_iff_fintype_card_le (admits := admits) (ρ := ρ) n).mp hAtMost)
      ((holds_atLeastCardinality_iff_fintype_card_ge (admits := admits) (ρ := ρ) n).mp hAtLeast)
  · intro hEq
    constructor
    · exact (holds_atLeastCardinality_iff_fintype_card_ge (admits := admits) (ρ := ρ) n).mpr
        (by simp [hEq])
    · exact (holds_atMostCardinality_iff_fintype_card_le (admits := admits) (ρ := ρ) n).mpr
        (by simp [hEq])

end HeytingLean.ModalCategorySets.Framework.Equality
