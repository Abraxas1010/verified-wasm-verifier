import Batteries.Data.Fin.Lemmas
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.OfFn

import HeytingLean.Layouts.Tuple.ToLayout
import HeytingLean.Layouts.Flat.Basic

/-!
# Realization (semantics) of `Tuple` morphisms

`Tuple` morphisms encode (tractable) flat layouts. This file exposes:

- `Mor.evalNat` : the raw layout function `Fin (size S) → ℕ` computed from `toLayout`,
- `Mor.eval`    : the tightened semantic map `Fin (size S) → Fin (size T)`.
-/

namespace HeytingLean
namespace Layouts
namespace Tuple

open Flat

namespace Obj

/-- Colexicographic unranking (shape-only). -/
def toCoords : Obj → ℕ → List ℕ
  | [], _ => []
  | s :: ss, i => (i % s.val) :: toCoords ss (i / s.val)

theorem toCoords_length (S : Obj) (i : ℕ) : (toCoords S i).length = S.length := by
  induction S generalizing i with
  | nil => simp [toCoords]
  | cons s ss ih => simp [toCoords, ih]

theorem toCoords_get_lt (S : Obj) (i : ℕ) (j : Fin S.length) :
    (toCoords S i).get ⟨j.val, lt_of_lt_of_eq j.isLt (toCoords_length S i).symm⟩ < (S.get j).val := by
  induction S generalizing i with
  | nil =>
      exact (Fin.elim0 j)
  | cons s ss ih =>
      cases j using Fin.cases with
      | zero =>
          simp [toCoords]
          exact Nat.mod_lt _ s.pos
      | succ j =>
          simpa [toCoords, Obj.toCoords_length] using ih (i := i / s.val) (j := j)

/-- Colexicographic ranking (shape-only). -/
def colexRank : Obj → List ℕ → ℕ
  | [], _ => 0
  | s :: ss, [] => s.val * colexRank ss []
  | s :: ss, x :: xs => x + s.val * colexRank ss xs

private theorem foldl_mul_left (a : ℕ) (S : Obj) (b : ℕ) :
    List.foldl (fun acc s => acc * s.val) (a * b) S =
      a * List.foldl (fun acc s => acc * s.val) b S := by
  induction S generalizing b with
  | nil => simp
  | cons s ss ih =>
      simp [List.foldl, ih, Nat.mul_assoc]

theorem size_cons (s : ℕ+) (ss : Obj) : Obj.size (s :: ss) = s.val * Obj.size ss := by
  unfold Obj.size
  simp [List.foldl]
  simpa [Obj.size] using (foldl_mul_left (a := s.val) (S := ss) (b := 1))

theorem size_pos (S : Obj) : 0 < Obj.size S := by
  induction S with
  | nil =>
      simp [Obj.size]
  | cons s ss ih =>
      simpa [size_cons] using Nat.mul_pos s.pos ih

theorem toCoords_colexRank (S : Obj) (coords : List ℕ)
    (hLen : coords.length = S.length)
    (hBound : ∀ j : Fin S.length,
      coords.get ⟨j.val, lt_of_lt_of_eq j.isLt hLen.symm⟩ < (S.get j).val) :
    toCoords S (colexRank S coords) = coords := by
  induction S generalizing coords with
  | nil =>
      cases coords with
      | nil =>
          simp [toCoords]
      | cons x xs =>
          -- `coords.length = 0` contradicts `coords = x :: xs`.
          simp at hLen
  | cons s ss ih =>
      cases coords with
      | nil =>
          simp at hLen
      | cons x xs =>
          have hLen' : xs.length = ss.length := by
            have h := congrArg Nat.pred hLen
            simp at h
            exact h
          have hx : x < s.val := by
            have h0 := hBound ⟨0, Nat.succ_pos _⟩
            simp at h0
            exact h0
          have hBound' : ∀ j : Fin ss.length,
              xs.get ⟨j.val, lt_of_lt_of_eq j.isLt hLen'.symm⟩ < (ss.get j).val := by
            intro j
            have h := hBound ⟨j.val.succ, Nat.succ_lt_succ j.isLt⟩
            simp at h
            exact h
          simp [toCoords, colexRank, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx,
            Nat.add_mul_div_left, Nat.div_eq_of_lt hx, ih xs hLen' hBound']

theorem colexRank_toCoords_of_lt_size (S : Obj) (i : ℕ) (hi : i < Obj.size S) :
    colexRank S (toCoords S i) = i := by
  induction S generalizing i with
  | nil =>
      have : i = 0 := Nat.lt_one_iff.mp hi
      subst this
      simp [colexRank]
  | cons s ss ih =>
      have hi' : i / s.val < Obj.size ss := by
        have : i < s.val * Obj.size ss := lt_of_lt_of_eq hi (size_cons s ss)
        exact Nat.div_lt_of_lt_mul this
      simp [toCoords, colexRank, ih (i := i / s.val) hi', Nat.mod_add_div]

theorem colexRank_lt_size (S : Obj) (coords : List ℕ)
    (hLen : coords.length = S.length)
    (hBound : ∀ j : Fin S.length,
      coords.get ⟨j.val, lt_of_lt_of_eq j.isLt hLen.symm⟩ < (S.get j).val) :
    colexRank S coords < Obj.size S := by
  induction S generalizing coords with
  | nil =>
      simp [colexRank, Obj.size]
  | cons s ss ih =>
      cases coords with
      | nil =>
          simp at hLen
      | cons x xs =>
          have hLen' : xs.length = ss.length := by
            have h := congrArg Nat.pred hLen
            simp at h
            exact h
          have hx_lt : x < s.val := by
            have h0 := hBound ⟨0, Nat.succ_pos _⟩
            simp at h0
            exact h0
          have hx_le : x ≤ s.val.pred := Nat.le_pred_of_lt hx_lt
          have hBound' : ∀ j : Fin ss.length,
              xs.get ⟨j.val, lt_of_lt_of_eq j.isLt hLen'.symm⟩ < (ss.get j).val := by
            intro j
            have h := hBound ⟨j.val.succ, Nat.succ_lt_succ j.isLt⟩
            simp at h
            exact h
          have hRest_lt : colexRank ss xs < Obj.size ss := ih (coords := xs) hLen' hBound'
          have hRest_le : colexRank ss xs ≤ (Obj.size ss).pred := Nat.le_pred_of_lt hRest_lt
          have hs_pos : 0 < s.val := s.pos
          have hSize_pos : 0 < Obj.size ss := size_pos ss
          have hmul : s.val * colexRank ss xs ≤ s.val * (Obj.size ss).pred :=
            Nat.mul_le_mul_left _ hRest_le
          have hadd : x + s.val * colexRank ss xs ≤ s.val.pred + s.val * (Obj.size ss).pred :=
            Nat.add_le_add hx_le hmul
          have hEq : s.val.pred + s.val * (Obj.size ss).pred + 1 = s.val * Obj.size ss := by
            have hs1 : 1 ≤ s.val := Nat.succ_le_of_lt hs_pos
            have hSize1 : 1 ≤ Obj.size ss := Nat.succ_le_of_lt hSize_pos
            have ha : s.val - 1 + 1 = s.val := Nat.sub_add_cancel hs1
            have hb : Obj.size ss - 1 + 1 = Obj.size ss := Nat.sub_add_cancel hSize1
            calc
              s.val.pred + s.val * (Obj.size ss).pred + 1
                  = (s.val - 1) + s.val * (Obj.size ss - 1) + 1 := by
                      simp [Nat.pred_eq_sub_one]
              _ = (s.val - 1) + 1 + s.val * (Obj.size ss - 1) := by
                      simp [Nat.add_assoc, Nat.add_comm]
              _ = s.val + s.val * (Obj.size ss - 1) := by
                      simp [ha]
              _ = s.val * (Obj.size ss - 1) + s.val := by
                      simp [Nat.add_comm]
              _ = s.val * ((Obj.size ss - 1) + 1) := by
                      simp [Nat.mul_add, Nat.mul_one]
              _ = s.val * Obj.size ss := by
                      simp [hb]
          have hSucc : x + s.val * colexRank ss xs + 1 ≤ s.val * Obj.size ss := by
            have h1 :
                x + s.val * colexRank ss xs + 1 ≤ s.val.pred + s.val * (Obj.size ss).pred + 1 :=
              Nat.add_le_add_right hadd 1
            exact le_trans h1 (le_of_eq hEq)
          have hlt :
              x + s.val * colexRank ss xs < s.val * Obj.size ss := by
            exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hSucc
          simpa [colexRank, size_cons] using hlt

end Obj

namespace Mor

variable {S T : Obj}

/-- Evaluate the encoded layout function on a *linear* index in `[0, size S)`. -/
def evalNat (f : Mor S T) (i : Fin (Obj.size S)) : ℕ :=
  FlatLayout.applyIndex f.toLayout i.val

/-- Evaluate on an explicit coordinate vector (colex coordinates in `S`). -/
def evalCoords (f : Mor S T) (coords : List ℕ) : ℕ :=
  FlatLayout.apply f.toLayout coords

/-- Search (computably) for a source index mapping to `j`. -/
def preimage? (f : Mor S T) (j : Fin T.length) : Option (Fin S.length) :=
  Fin.find? (fun i => decide (f.hom (some i) = some j))

theorem preimage?_eq_some_map (f : Mor S T) (j : Fin T.length) (i : Fin S.length)
    (h : f.preimage? j = some i) : f.hom (some i) = some j := by
  have h' := h
  dsimp [preimage?] at h'
  have : decide (f.hom (some i) = some j) = true :=
    Fin.eq_true_of_find?_eq_some (p := fun i => decide (f.hom (some i) = some j)) h'
  exact (decide_eq_true_iff.mp this)

theorem preimage?_eq_none_map (f : Mor S T) (j : Fin T.length) (h : f.preimage? j = none) :
    ∀ i : Fin S.length, f.hom (some i) ≠ some j := by
  intro i hi
  have h' := h
  dsimp [preimage?] at h'
  have : decide (f.hom (some i) = some j) = false :=
    Fin.eq_false_of_find?_eq_none (p := fun i => decide (f.hom (some i) = some j)) h' i
  exact (decide_eq_false_iff_not.mp this) hi

theorem preimage?_eq_some_of_map (f : Mor S T) (i : Fin S.length) (j : Fin T.length)
    (h : f.hom (some i) = some j) : f.preimage? j = some i := by
  dsimp [preimage?]
  apply (Fin.find?_eq_some_iff (p := fun k => decide (f.hom (some k) = some j))).2
  constructor
  · exact decide_eq_true_iff.2 h
  · intro i' hi'
    apply decide_eq_false_iff_not.2
    intro hiEq
    have eq := f.inj_away i i' j h hiEq
    have hi'' := hi'
    simp [eq] at hi''

/-- Scatter `S`-coordinates into `T`-coordinates according to a `Tuple` morphism. -/
def scatterCoords (f : Mor S T) (coordsS : List ℕ) (hLen : coordsS.length = S.length) : List ℕ :=
  List.ofFn (fun j : Fin T.length =>
    match f.preimage? j with
    | none => 0
    | some i => coordsS.get ⟨i.val, lt_of_lt_of_eq i.isLt hLen.symm⟩)

theorem scatterCoords_length (f : Mor S T) (coordsS : List ℕ) (hLen : coordsS.length = S.length) :
    (f.scatterCoords coordsS hLen).length = T.length := by
  simp [scatterCoords]

theorem scatterCoords_get (f : Mor S T) (coordsS : List ℕ) (hLen : coordsS.length = S.length) (j : Fin T.length) :
    (f.scatterCoords coordsS hLen).get
        ⟨j.val,
          lt_of_lt_of_eq j.isLt (scatterCoords_length (f := f) (coordsS := coordsS) (hLen := hLen)).symm⟩ =
      match f.preimage? j with
      | none => 0
      | some i => coordsS.get ⟨i.val, lt_of_lt_of_eq i.isLt hLen.symm⟩ := by
  simp [scatterCoords]

theorem scatterCoords_bound (f : Mor S T) (coordsS : List ℕ) (hLen : coordsS.length = S.length)
    (hBound : ∀ i : Fin S.length,
      coordsS.get ⟨i.val, lt_of_lt_of_eq i.isLt hLen.symm⟩ < (S.get i).val) :
    ∀ j : Fin T.length,
      (f.scatterCoords coordsS hLen).get
          ⟨j.val,
            lt_of_lt_of_eq j.isLt (scatterCoords_length (f := f) (coordsS := coordsS) (hLen := hLen)).symm⟩ <
        (T.get j).val := by
  intro j
  simp [scatterCoords]
  cases hj : f.preimage? j with
  | none =>
      exact (T.get j).pos
  | some src =>
      have hMap : f.hom (some src) = some j := f.preimage?_eq_some_map j src hj
      have hCoord : coordsS.get ⟨src.val, lt_of_lt_of_eq src.isLt hLen.symm⟩ < (S.get src).val :=
        hBound src
      have hShape : S.get src = T.get j := f.dim_pres src j hMap
      have : (S.get src).val = (T.get j).val := congrArg PNat.val hShape
      exact lt_of_lt_of_eq hCoord this

theorem preimage?_comp {U : Obj} (g : Mor T U) (f : Mor S T) (k : Fin U.length) :
    (Mor.comp g f).preimage? k =
      match g.preimage? k with
      | none => none
      | some j => f.preimage? j := by
  classical
  cases hg : g.preimage? k with
  | none =>
      dsimp [preimage?]
      apply (Fin.find?_eq_none_iff (p := fun i => decide ((Mor.comp g f).hom (some i) = some k))).2
      intro i
      apply decide_eq_false_iff_not.2
      intro hi
      cases hfi : f.hom (some i) with
      | none =>
          have : g.hom none = some k := by
            simpa [Mor.comp, Fin0Hom.comp_apply, hfi] using hi
          simp [g.hom.map_base] at this
      | some j =>
          have hgNo : ∀ j' : Fin T.length, g.hom (some j') ≠ some k :=
            g.preimage?_eq_none_map (j := k) hg
          have : g.hom (some j) = some k := by
            simpa [Mor.comp, Fin0Hom.comp_apply, hfi] using hi
          exact hgNo j this
  | some j =>
      cases hf : f.preimage? j with
      | none =>
          simp [hf]
          dsimp [preimage?]
          apply (Fin.find?_eq_none_iff (p := fun i => decide ((Mor.comp g f).hom (some i) = some k))).2
          intro i
          apply decide_eq_false_iff_not.2
          intro hi
          have hgMap : g.hom (some j) = some k := g.preimage?_eq_some_map (j := k) (i := j) hg
          cases hfi : f.hom (some i) with
          | none =>
              have : g.hom none = some k := by
                simpa [Mor.comp, Fin0Hom.comp_apply, hfi] using hi
              simp [g.hom.map_base] at this
          | some j' =>
              have hg' : g.hom (some j') = some k := by
                simpa [Mor.comp, Fin0Hom.comp_apply, hfi] using hi
              have hj : j = j' := g.inj_away j j' k hgMap hg'
              cases hj
              exact (f.preimage?_eq_none_map (j := j) hf i) hfi
      | some i =>
          simp [hf]
          dsimp [preimage?]
          apply (Fin.find?_eq_some_iff (p := fun i => decide ((Mor.comp g f).hom (some i) = some k))).2
          constructor
          · have hfMap : f.hom (some i) = some j := f.preimage?_eq_some_map (j := j) (i := i) hf
            have hgMap : g.hom (some j) = some k := g.preimage?_eq_some_map (j := k) (i := j) hg
            have : (Mor.comp g f).hom (some i) = some k := by
              simpa [Mor.comp, Fin0Hom.comp_apply, hfMap] using hgMap
            exact decide_eq_true_iff.2 this
          · intro i' hi'
            apply decide_eq_false_iff_not.2
            intro hiEq
            have hfMap : f.hom (some i) = some j := f.preimage?_eq_some_map (j := j) (i := i) hf
            have hgMap : g.hom (some j) = some k := g.preimage?_eq_some_map (j := k) (i := j) hg
            cases hfi' : f.hom (some i') with
            | none =>
                have : g.hom none = some k := by
                  simpa [Mor.comp, Fin0Hom.comp_apply, hfi'] using hiEq
                simp [g.hom.map_base] at this
            | some j' =>
                have hg' : g.hom (some j') = some k := by
                  simpa [Mor.comp, Fin0Hom.comp_apply, hfi'] using hiEq
                have hj : j = j' := g.inj_away j j' k hgMap hg'
                cases hj
                have hii' : i = i' := f.inj_away i i' j hfMap hfi'
                have hi'' := hi'
                simp [hii'] at hi''

theorem scatterCoords_comp {U : Obj} (g : Mor T U) (f : Mor S T) (coordsS : List ℕ)
    (hLenS : coordsS.length = S.length) :
    (Mor.comp g f).scatterCoords coordsS hLenS =
      g.scatterCoords (f.scatterCoords coordsS hLenS)
        (f.scatterCoords_length (coordsS := coordsS) (hLen := hLenS)) := by
  unfold scatterCoords
  apply (List.ofFn_inj).2
  funext k
  cases hg : g.preimage? k with
  | none =>
      simp [preimage?_comp, hg]
  | some j =>
      cases hf : f.preimage? j with
      | none =>
          simp [preimage?_comp, hg, hf]
      | some i =>
          simp [preimage?_comp, hg, hf]

theorem scatterCoords_congr (f : Mor S T) (coords : List ℕ) (hLen₁ hLen₂ : coords.length = S.length) :
    f.scatterCoords coords hLen₁ = f.scatterCoords coords hLen₂ := by
  unfold scatterCoords
  apply (List.ofFn_inj).2
  funext j
  cases hj : f.preimage? j with
  | none =>
      rfl
  | some i =>
      have hIdx :
          (⟨i.val, lt_of_lt_of_eq i.isLt hLen₁.symm⟩ : Fin coords.length) =
            ⟨i.val, lt_of_lt_of_eq i.isLt hLen₂.symm⟩ := by
        apply Fin.ext
        rfl
      simp [hIdx]

theorem scatterCoords_congr_of_eq (f : Mor S T) {coords₁ coords₂ : List ℕ}
    (h : coords₁ = coords₂) (hLen₁ : coords₁.length = S.length) (hLen₂ : coords₂.length = S.length) :
    f.scatterCoords coords₁ hLen₁ = f.scatterCoords coords₂ hLen₂ := by
  subst h
  exact scatterCoords_congr (f := f) (coords := coords₁) hLen₁ hLen₂

/-- Tightened realization: `Tuple` morphisms land in `[0, size T)`. -/
def eval (f : Mor S T) (i : Fin (Obj.size S)) : Fin (Obj.size T) :=
  let coordsS := Obj.toCoords S i.val
  let hLenS : coordsS.length = S.length := Obj.toCoords_length S i.val
  let coordsT := f.scatterCoords coordsS hLenS
  let v := Obj.colexRank T coordsT
  have hLenT : coordsT.length = T.length := by
    dsimp [coordsT]
    exact f.scatterCoords_length (coordsS := coordsS) (hLen := hLenS)
  have hBoundT :
      ∀ j : Fin T.length,
        coordsT.get ⟨j.val, lt_of_lt_of_eq j.isLt hLenT.symm⟩ < (T.get j).val := by
    dsimp [coordsT]
    exact f.scatterCoords_bound (coordsS := coordsS) (hLen := hLenS)
      (hBound := fun j => Obj.toCoords_get_lt (S := S) (i := i.val) j)
  have hv : v < Obj.size T := Obj.colexRank_lt_size (S := T) (coords := coordsT) hLenT hBoundT
  ⟨v, hv⟩

theorem eval_val (f : Mor S T) (i : Fin (Obj.size S)) :
    (f.eval i).val = Obj.colexRank T (f.scatterCoords (Obj.toCoords S i.val) (Obj.toCoords_length S i.val)) := rfl

theorem toCoords_eval_val (f : Mor S T) (i : Fin (Obj.size S)) :
    Obj.toCoords T (f.eval i).val =
      f.scatterCoords (Obj.toCoords S i.val) (Obj.toCoords_length S i.val) := by
  let coordsS := Obj.toCoords S i.val
  have hLenS : coordsS.length = S.length := Obj.toCoords_length S i.val
  let coordsT := f.scatterCoords coordsS hLenS
  have hLenT : coordsT.length = T.length := f.scatterCoords_length (coordsS := coordsS) (hLen := hLenS)
  have hBoundT :
      ∀ j : Fin T.length,
        coordsT.get ⟨j.val, lt_of_lt_of_eq j.isLt hLenT.symm⟩ < (T.get j).val := by
    exact f.scatterCoords_bound (coordsS := coordsS) (hLen := hLenS)
      (hBound := fun j => Obj.toCoords_get_lt (S := S) (i := i.val) j)
  have h :
      Obj.toCoords T (Obj.colexRank T coordsT) = coordsT :=
    Obj.toCoords_colexRank (S := T) (coords := coordsT) hLenT hBoundT
  simpa [Mor.eval, coordsS, coordsT, hLenS] using h

theorem scatterCoords_id (S : Obj) (coords : List ℕ) (hLen : coords.length = S.length) :
    (Mor.id S).scatterCoords coords hLen = coords := by
  unfold scatterCoords
  have hPre : ∀ j : Fin S.length, (Mor.id S).preimage? j = some j := by
    intro j
    apply (Mor.id S).preimage?_eq_some_of_map (i := j) (j := j)
    simp [Mor.id]
  simp [hPre]
  -- `simp` renders the output as `List.ofFn (fun j : Fin S.length => coords[(j : Nat)])`.
  -- Convert this `ofFn` to have domain `Fin coords.length`, then close via `List.ofFn_getElem`.
  have hCong :
      (List.ofFn fun j : Fin S.length => coords[(j : Nat)]) =
        List.ofFn (fun j : Fin coords.length => coords[(j : Nat)]) := by
    simp [List.ofFn_congr (h := hLen.symm) (f := fun j : Fin S.length => coords[(j : Nat)])]
  -- Now conclude using the canonical `ofFn`-presentation of a list.
  rw [hCong]
  exact List.ofFn_getElem coords

theorem eval_id (S : Obj) (i : Fin (Obj.size S)) : (Mor.id S).eval i = i := by
  apply Fin.ext
  simp [Mor.eval, scatterCoords_id, Obj.colexRank_toCoords_of_lt_size, i.isLt]

theorem eval_comp {U : Obj} (f : Mor S T) (g : Mor T U) (i : Fin (Obj.size S)) :
    (Mor.comp g f).eval i = g.eval (f.eval i) := by
  apply Fin.ext
  have hCoords :
      Obj.toCoords T (f.eval i).val =
        f.scatterCoords (Obj.toCoords S i.val) (Obj.toCoords_length S i.val) :=
    f.toCoords_eval_val i
  have hScatter :
      g.scatterCoords (Obj.toCoords T (f.eval i).val) (Obj.toCoords_length T (f.eval i).val) =
        g.scatterCoords (f.scatterCoords (Obj.toCoords S i.val) (Obj.toCoords_length S i.val))
          (f.scatterCoords_length (coordsS := Obj.toCoords S i.val) (hLen := Obj.toCoords_length S i.val)) :=
    scatterCoords_congr_of_eq (f := g) (h := hCoords)
      (hLen₁ := Obj.toCoords_length T (f.eval i).val)
      (hLen₂ := f.scatterCoords_length (coordsS := Obj.toCoords S i.val) (hLen := Obj.toCoords_length S i.val))
  rw [Mor.eval_val (f := Mor.comp g f) (i := i)]
  rw [Mor.eval_val (f := g) (i := f.eval i)]
  rw [scatterCoords_comp (g := g) (f := f) (coordsS := Obj.toCoords S i.val)
    (hLenS := Obj.toCoords_length S i.val)]
  rw [hScatter]

end Mor

end Tuple
end Layouts
end HeytingLean
