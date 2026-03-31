import Mathlib.SetTheory.Ordinal.Notation

/-!
# Constructive ordinal notation (below ε₀)

This module provides a small, executable ordinal-notation layer for use in
toy "transfinite birthday" extensions.

Implementation note:
We reuse Mathlib's `NONote` (normal-form ordinal notations for ordinals below `ε₀`),
which comes with computable comparison and arithmetic on Cantor normal forms.
-/

namespace HeytingLean
namespace Numbers
namespace Ordinal

/-- Cantor-normal-form ordinal notation (below ε₀), backed by `Mathlib`'s `NONote`. -/
abbrev OrdinalCNF := NONote

namespace OrdinalCNF

open ONote

/-- Embed a natural number as an ordinal notation. -/
def ofNat (n : Nat) : OrdinalCNF :=
  NONote.ofNat n

/-- The ordinal notation for `ω`. -/
def omega : OrdinalCNF :=
  -- Avoid relying on typeclass unfolding of `ONote.omega` during `NONote.mk`.
  NONote.mk (ONote.oadd (ONote.ofNat 1) (1 : ℕ+) 0)

/-- Compare ordinal notations (computable). -/
def compare (a b : OrdinalCNF) : Ordering :=
  NONote.cmp a b

/-- Max of two ordinal notations (computable). -/
def max (a b : OrdinalCNF) : OrdinalCNF :=
  if compare a b == .lt then b else a

/-- Successor ordinal `α + 1`. -/
def succ (a : OrdinalCNF) : OrdinalCNF :=
  a + ofNat 1

/-- Supremum of a finite list (constructive and computable). -/
def supList : List OrdinalCNF → OrdinalCNF
  | [] => 0
  | x :: xs => xs.foldl max x

@[simp] theorem supList_nil : supList [] = (0 : OrdinalCNF) := rfl

@[simp] theorem supList_singleton (a : OrdinalCNF) : supList [a] = a := by
  simp [supList]

@[simp] theorem max_zero_right (a : OrdinalCNF) : max a 0 = a := by
  cases a with
  | mk o ho =>
      cases o <;> simp [max, compare, NONote.cmp, ONote.cmp]

theorem compare_eq_lt_iff_lt (a b : OrdinalCNF) :
    compare a b = Ordering.lt ↔ a < b := by
  have hcmp : (NONote.cmp a b).Compares a b := NONote.cmp_compares a b
  constructor
  · intro h
    exact (hcmp.eq_lt).1 (by simpa [compare] using h)
  · intro h
    simpa [compare] using (hcmp.eq_lt).2 h

theorem compare_eq_eq_iff_eq (a b : OrdinalCNF) :
    compare a b = Ordering.eq ↔ a = b := by
  have hcmp : (NONote.cmp a b).Compares a b := NONote.cmp_compares a b
  constructor
  · intro h
    exact (hcmp.eq_eq).1 (by simpa [compare] using h)
  · intro h
    simpa [compare] using (hcmp.eq_eq).2 h

theorem compare_eq_gt_iff_lt (a b : OrdinalCNF) :
    compare a b = Ordering.gt ↔ b < a := by
  have hcmp : (NONote.cmp a b).Compares a b := NONote.cmp_compares a b
  constructor
  · intro h
    exact (hcmp.eq_gt).1 (by simpa [compare] using h)
  · intro h
    simpa [compare] using (hcmp.eq_gt).2 h

theorem max_eq_right_of_le {a b : OrdinalCNF} (h : a ≤ b) : max a b = b := by
  unfold max
  by_cases hlt : compare a b = Ordering.lt
  · simp [hlt]
  · have hEq : a = b := by
      exact (le_antisymm h (le_of_not_gt (by
        intro hba
        exact hlt ((compare_eq_lt_iff_lt a b).2 hba))))
    simp [hEq]

theorem max_eq_left_of_ge {a b : OrdinalCNF} (h : b ≤ a) : max a b = a := by
  unfold max
  have hnot : compare a b ≠ Ordering.lt := by
    intro hlt
    exact (not_lt_of_ge h) ((compare_eq_lt_iff_lt a b).1 hlt)
  simp [hnot]

theorem le_max_left (a b : OrdinalCNF) : a ≤ max a b := by
  by_cases h : a ≤ b
  · rw [max_eq_right_of_le h]
    exact h
  · have hba : b ≤ a := le_of_not_ge h
    rw [max_eq_left_of_ge hba]

theorem le_max_right (a b : OrdinalCNF) : b ≤ max a b := by
  by_cases h : a ≤ b
  · rw [max_eq_right_of_le h]
  · have hba : b ≤ a := le_of_not_ge h
    rw [max_eq_left_of_ge hba]
    exact hba

theorem max_le {a b c : OrdinalCNF} (ha : a ≤ c) (hb : b ≤ c) :
    max a b ≤ c := by
  by_cases h : a ≤ b
  · rw [max_eq_right_of_le h]
    exact hb
  · have hba : b ≤ a := le_of_not_ge h
    rw [max_eq_left_of_ge hba]
    exact ha

theorem max_comm (a b : OrdinalCNF) : max a b = max b a :=
  le_antisymm
    (max_le (le_max_right b a) (le_max_left b a))
    (max_le (le_max_right a b) (le_max_left a b))

private theorem foldl_max_le :
    ∀ (xs : List OrdinalCNF) (acc bound : OrdinalCNF),
      acc ≤ bound →
      (∀ x ∈ xs, x ≤ bound) →
      List.foldl (fun a x => max a x) acc xs ≤ bound
  | [], acc, bound, hacc, _ => by
      simpa using hacc
  | x :: xs, acc, bound, hacc, hxs => by
      have hx : x ≤ bound := hxs x (by simp)
      have hacc' : max acc x ≤ bound := max_le hacc hx
      exact foldl_max_le xs (max acc x) bound hacc' (by
        intro y hy
        exact hxs y (by simp [hy]))

private theorem foldl_max_acc_le :
    ∀ (xs : List OrdinalCNF) (acc : OrdinalCNF),
      acc ≤ List.foldl (fun a x => max a x) acc xs
  | [], acc => by
      simp
  | x :: xs, acc => by
      have hstep : acc ≤ max acc x := le_max_left acc x
      exact le_trans hstep (foldl_max_acc_le xs (max acc x))

theorem supList_le_of_forall {xs : List OrdinalCNF} {bound : OrdinalCNF}
    (hxs : ∀ x ∈ xs, x ≤ bound) :
    supList xs ≤ bound := by
  cases xs with
  | nil =>
      change (0 : OrdinalCNF) ≤ bound
      change (0 : Ordinal) ≤ NONote.repr bound
      simp
  | cons x xs =>
      exact foldl_max_le xs x bound (hxs x (by simp)) (by
        intro y hy
        exact hxs y (by simp [hy]))

theorem le_supList_of_mem {xs : List OrdinalCNF} {x : OrdinalCNF}
    (hx : x ∈ xs) :
    x ≤ supList xs := by
  cases xs with
  | nil =>
      cases hx
  | cons y ys =>
      simp at hx
      cases hx with
      | inl hxy =>
          subst x
          simp [supList]
          exact foldl_max_acc_le ys y
      | inr hxys =>
          have hx' :
              ∀ {acc : OrdinalCNF} {zs : List OrdinalCNF},
                x ∈ zs → x ≤ List.foldl (fun a z => max a z) acc zs := by
            intro acc zs hmem
            induction zs generalizing acc with
            | nil =>
                cases hmem
            | cons z zs ih =>
                simp at hmem
                cases hmem with
                | inl h =>
                    subst x
                    exact le_trans (le_max_right acc z) (foldl_max_acc_le zs (max acc z))
                | inr h =>
                    exact ih h
          have hfold : x ≤ List.foldl (fun a z => max a z) y ys := hx' hxys
          simpa [supList] using hfold

theorem add_le_add_right {a b c : OrdinalCNF} (h : a ≤ b) : a + c ≤ b + c := by
  have hrepr : NONote.repr a ≤ NONote.repr b := h
  change NONote.repr (a + c) ≤ NONote.repr (b + c)
  rw [NONote.repr_add, NONote.repr_add]
  exact _root_.add_le_add_right hrepr (NONote.repr c)

theorem add_le_add_left {a b c : OrdinalCNF} (h : a ≤ b) : c + a ≤ c + b := by
  have hrepr : NONote.repr a ≤ NONote.repr b := h
  change NONote.repr (c + a) ≤ NONote.repr (c + b)
  rw [NONote.repr_add, NONote.repr_add]
  exact _root_.add_le_add_left hrepr (NONote.repr c)

theorem add_assoc (a b c : OrdinalCNF) : (a + b) + c = a + (b + c) := by
  have hrepr : NONote.repr ((a + b) + c) = NONote.repr (a + (b + c)) := by
    rw [NONote.repr_add, NONote.repr_add, NONote.repr_add, NONote.repr_add]
    exact _root_.add_assoc (NONote.repr a) (NONote.repr b) (NONote.repr c)
  have hle : (a + b) + c ≤ a + (b + c) := by
    change NONote.repr ((a + b) + c) ≤ NONote.repr (a + (b + c))
    exact le_of_eq hrepr
  have hge : a + (b + c) ≤ (a + b) + c := by
    change NONote.repr (a + (b + c)) ≤ NONote.repr ((a + b) + c)
    exact ge_of_eq hrepr
  exact le_antisymm hle hge

theorem le_add_right (a b : OrdinalCNF) : a ≤ a + b := by
  change NONote.repr a ≤ NONote.repr (a + b)
  simp [NONote.repr_add]

@[simp] theorem ofNat_add_one (n : Nat) :
    ofNat n + ofNat 1 = ofNat (n + 1) := by
  have hrepr :
      NONote.repr (ofNat n + ofNat 1) = NONote.repr (ofNat (n + 1)) := by
    rw [NONote.repr_add]
    simp [ofNat, NONote.ofNat, NONote.repr]
  have hle : ofNat n + ofNat 1 ≤ ofNat (n + 1) := by
    change NONote.repr (ofNat n + ofNat 1) ≤ NONote.repr (ofNat (n + 1))
    exact le_of_eq hrepr
  have hge : ofNat (n + 1) ≤ ofNat n + ofNat 1 := by
    change NONote.repr (ofNat (n + 1)) ≤ NONote.repr (ofNat n + ofNat 1)
    exact ge_of_eq hrepr
  exact le_antisymm hle hge

theorem ofNat_add_one_succ (n : Nat) :
    ofNat n + ofNat 1 = ofNat (Nat.succ n) := by
  simp [Nat.succ_eq_add_one, ofNat_add_one]

end OrdinalCNF

/-- Prefer equality decision via `NONote.cmp`, not structural equality of the underlying `ONote`.

This keeps `decide`-based sanity checks executable even though `ONote` contains `ℕ+` (a subtype). -/
instance (priority := 1000) : DecidableEq OrdinalCNF := by
  intro a b
  cases h : NONote.cmp a b with
  | lt =>
      refine isFalse (fun hab => ?_)
      have hc : (NONote.cmp a b).Compares a b := NONote.cmp_compares a b
      have hab' : a < b := by simpa [h] using hc
      have : a < a := by
        cases hab
        exact hab'
      exact lt_irrefl _ this
  | eq =>
      refine isTrue ?_
      have hc : (NONote.cmp a b).Compares a b := NONote.cmp_compares a b
      simpa [h] using hc
  | gt =>
      refine isFalse (fun hab => ?_)
      have hc : (NONote.cmp a b).Compares a b := NONote.cmp_compares a b
      have hab' : a > b := by simpa [h] using hc
      have : a > a := by
        cases hab
        exact hab'
      exact lt_irrefl _ this

end Ordinal
end Numbers
end HeytingLean
