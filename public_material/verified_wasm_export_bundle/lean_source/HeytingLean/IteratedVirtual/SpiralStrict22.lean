import Mathlib.Data.Real.Basic
import HeytingLean.IteratedVirtual.StrictN

/-!
# IteratedVirtual.SpiralStrict22

A tiny strict 22-category whose **top (22)-cells** are “spiral parameters”.

This makes the slogan “the spiral is a 22-cell in a higher category” *literally representable*
as a globe-map `GlobeN 22 ⟶ Cat₍22₎`.
-/

namespace HeytingLean
namespace IteratedVirtual

structure SpiralParamsR where
  count : Nat
  step : ℝ
  pitch : ℝ

namespace SpiralParamsR

instance : Zero SpiralParamsR :=
  ⟨{ count := 0, step := 0, pitch := 0 }⟩

instance : Add SpiralParamsR :=
  ⟨fun a b => { count := a.count + b.count, step := a.step + b.step, pitch := a.pitch + b.pitch }⟩

@[simp] theorem zero_count : (0 : SpiralParamsR).count = 0 := rfl
@[simp] theorem zero_step : (0 : SpiralParamsR).step = 0 := rfl
@[simp] theorem zero_pitch : (0 : SpiralParamsR).pitch = 0 := rfl

@[simp] theorem add_def (a b : SpiralParamsR) :
    a + b = { count := a.count + b.count, step := a.step + b.step, pitch := a.pitch + b.pitch } := rfl

theorem add_assoc (a b c : SpiralParamsR) : (a + b) + c = a + (b + c) := by
  cases a
  cases b
  cases c
  simp [add_def, _root_.add_assoc]

theorem zero_add (a : SpiralParamsR) : (0 : SpiralParamsR) + a = a := by
  cases a
  simp [add_def]

theorem add_zero (a : SpiralParamsR) : a + (0 : SpiralParamsR) = a := by
  cases a
  simp [add_def]

end SpiralParamsR

def spiral22Params : SpiralParamsR :=
  { count := 64
    step := 0.35
    pitch := 0.15 }

/-- Cell types for the spiral example: only dimension `22` carries data; all others are trivial. -/
def spiral22CellType (k : Nat) : Type :=
  if k = 22 then SpiralParamsR else PUnit

private def spiral22PUnitCell {k : Nat} (hk : k ≠ 22) : spiral22CellType k := by
  simpa [spiral22CellType, hk] using (PUnit.unit : PUnit)

private def spiral22Src (k : Nat) (hk : k < 22) : spiral22CellType (k + 1) → spiral22CellType k := by
  intro _
  exact spiral22PUnitCell (ne_of_lt hk)

private def spiral22Tgt (k : Nat) (hk : k < 22) : spiral22CellType (k + 1) → spiral22CellType k := by
  intro _
  exact spiral22PUnitCell (ne_of_lt hk)

private theorem spiral22CellType_subsingleton {k : Nat} (hk : k ≠ 22) : Subsingleton (spiral22CellType k) := by
  classical
  have : Subsingleton PUnit := by infer_instance
  simpa [spiral22CellType, hk] using this

/-- The underlying truncated globular set for the “spiral 22-category”. -/
def spiral22Globular : NGlobularSet 22 where
  Cell := spiral22CellType
  src := fun k hk => spiral22Src k hk
  tgt := fun k hk => spiral22Tgt k hk
  src_src_eq_src_tgt := by
    intro k hk0 hk1 x
    simp [spiral22Src]
  tgt_src_eq_tgt_tgt := by
    intro k hk0 hk1 x
    simp [spiral22Tgt]

def spiral22Cat : StrictNCategory 22 where
  G := spiral22Globular
  idCell := by
    intro k hk a
    by_cases h21 : k = 21
    · subst h21
      cases a
      refine ⟨(by simpa [spiral22Globular, spiral22CellType] using (0 : SpiralParamsR)), ?_, ?_⟩
      ·
        haveI : Subsingleton (spiral22Globular.Cell 21) :=
          spiral22CellType_subsingleton (k := 21) (ne_of_lt hk)
        exact Subsingleton.elim _ _
      ·
        haveI : Subsingleton (spiral22Globular.Cell 21) :=
          spiral22CellType_subsingleton (k := 21) (ne_of_lt hk)
        exact Subsingleton.elim _ _
    ·
      have hk1 : k + 1 ≠ 22 := by
        intro hk1Eq
        have hkEq : k = 21 := by
          have : k + 1 = 21 + 1 := by
            simpa using hk1Eq
          exact Nat.add_right_cancel this
        exact h21 hkEq
      refine ⟨(by simpa [spiral22Globular, spiral22CellType, hk1] using (PUnit.unit : PUnit)), ?_, ?_⟩
      ·
        haveI : Subsingleton (spiral22Globular.Cell k) :=
          spiral22CellType_subsingleton (k := k) (ne_of_lt hk)
        exact Subsingleton.elim _ _
      ·
        haveI : Subsingleton (spiral22Globular.Cell k) :=
          spiral22CellType_subsingleton (k := k) (ne_of_lt hk)
        exact Subsingleton.elim _ _
  compCell := by
    intro k hk a b c f g
    by_cases h21 : k = 21
    · subst h21
      cases a
      cases b
      cases c
      classical
      let fR : SpiralParamsR := by
        simpa [spiral22Globular, spiral22CellType] using f.1
      let gR : SpiralParamsR := by
        simpa [spiral22Globular, spiral22CellType] using g.1
      refine ⟨(by simpa [fR, gR, spiral22Globular, spiral22CellType] using (fR + gR)), ?_, ?_⟩
      ·
        haveI : Subsingleton (spiral22Globular.Cell 21) :=
          spiral22CellType_subsingleton (k := 21) (ne_of_lt hk)
        exact Subsingleton.elim _ _
      ·
        haveI : Subsingleton (spiral22Globular.Cell 21) :=
          spiral22CellType_subsingleton (k := 21) (ne_of_lt hk)
        exact Subsingleton.elim _ _
    ·
      have hk1 : k + 1 ≠ 22 := by
        intro hk1Eq
        have hkEq : k = 21 := by
          have : k + 1 = 21 + 1 := by
            simpa using hk1Eq
          exact Nat.add_right_cancel this
        exact h21 hkEq
      refine ⟨(by simpa [spiral22Globular, spiral22CellType, hk1] using (PUnit.unit : PUnit)), ?_, ?_⟩
      ·
        haveI : Subsingleton (spiral22Globular.Cell k) :=
          spiral22CellType_subsingleton (k := k) (ne_of_lt hk)
        exact Subsingleton.elim _ _
      ·
        haveI : Subsingleton (spiral22Globular.Cell k) :=
          spiral22CellType_subsingleton (k := k) (ne_of_lt hk)
        exact Subsingleton.elim _ _
  id_comp := by
    intro k hk a b f
    by_cases h21 : k = 21
    · subst h21
      cases a
      cases b
      cases f with
      | mk p hp =>
        apply Subtype.ext
        classical
        let pR : SpiralParamsR := by
          simpa [spiral22Globular, spiral22CellType] using p
        have : (0 : SpiralParamsR) + pR = pR := SpiralParamsR.zero_add pR
        simpa [pR, spiral22Globular, spiral22CellType] using this
    ·
      have hk1 : k + 1 ≠ 22 := by
        intro hk1Eq
        have hkEq : k = 21 := by
          have : k + 1 = 21 + 1 := by
            simpa using hk1Eq
          exact Nat.add_right_cancel this
        exact h21 hkEq
      haveI : Subsingleton (spiral22Globular.Cell (k + 1)) :=
        spiral22CellType_subsingleton (k := k + 1) hk1
      haveI :
          Subsingleton
            ({ f : spiral22Globular.Cell (k + 1) //
                spiral22Globular.src k hk f = a ∧ spiral22Globular.tgt k hk f = b }) := by
        infer_instance
      exact Subsingleton.elim _ _
  comp_id := by
    intro k hk a b f
    by_cases h21 : k = 21
    · subst h21
      cases a
      cases b
      cases f with
      | mk p hp =>
        apply Subtype.ext
        classical
        let pR : SpiralParamsR := by
          simpa [spiral22Globular, spiral22CellType] using p
        have : pR + (0 : SpiralParamsR) = pR := SpiralParamsR.add_zero pR
        simpa [pR, spiral22Globular, spiral22CellType] using this
    ·
      have hk1 : k + 1 ≠ 22 := by
        intro hk1Eq
        have hkEq : k = 21 := by
          have : k + 1 = 21 + 1 := by
            simpa using hk1Eq
          exact Nat.add_right_cancel this
        exact h21 hkEq
      haveI : Subsingleton (spiral22Globular.Cell (k + 1)) :=
        spiral22CellType_subsingleton (k := k + 1) hk1
      haveI :
          Subsingleton
            ({ f : spiral22Globular.Cell (k + 1) //
                spiral22Globular.src k hk f = a ∧ spiral22Globular.tgt k hk f = b }) := by
        infer_instance
      exact Subsingleton.elim _ _
  assoc := by
    intro k hk a b c d f g h
    by_cases h21 : k = 21
    · subst h21
      cases a
      cases b
      cases c
      cases d
      cases f with
      | mk fp hfp =>
        cases g with
        | mk gp hgp =>
          cases h with
          | mk hp hhp =>
            apply Subtype.ext
            classical
            let fpR : SpiralParamsR := by
              simpa [spiral22Globular, spiral22CellType] using fp
            let gpR : SpiralParamsR := by
              simpa [spiral22Globular, spiral22CellType] using gp
            let hpR : SpiralParamsR := by
              simpa [spiral22Globular, spiral22CellType] using hp
            have : (fpR + gpR) + hpR = fpR + (gpR + hpR) := SpiralParamsR.add_assoc fpR gpR hpR
            simpa [fpR, gpR, hpR, spiral22Globular, spiral22CellType] using this
    ·
      have hk1 : k + 1 ≠ 22 := by
        intro hk1Eq
        have hkEq : k = 21 := by
          have : k + 1 = 21 + 1 := by
            simpa using hk1Eq
          exact Nat.add_right_cancel this
        exact h21 hkEq
      haveI : Subsingleton (spiral22Globular.Cell (k + 1)) :=
        spiral22CellType_subsingleton (k := k + 1) hk1
      haveI :
          Subsingleton
            ({ f : spiral22Globular.Cell (k + 1) //
                spiral22Globular.src k hk f = a ∧ spiral22Globular.tgt k hk f = d }) := by
        infer_instance
      exact Subsingleton.elim _ _

/-- The “spiral as a 22-cell”: a map from the walking 22-globe into `spiral22Cat`. -/
def spiral22Cell : StrictNCategory.CellTop (n := 22) spiral22Cat :=
  { map := by
      intro k _
      by_cases h : k = 22
      · subst h
        exact spiral22Params
      · exact spiral22PUnitCell h
    map_src := by
      intro k hk x
      haveI : Subsingleton (spiral22Cat.G.Cell k) :=
        spiral22CellType_subsingleton (k := k) (ne_of_lt hk)
      exact Subsingleton.elim _ _
    map_tgt := by
      intro k hk x
      haveI : Subsingleton (spiral22Cat.G.Cell k) :=
        spiral22CellType_subsingleton (k := k) (ne_of_lt hk)
      exact Subsingleton.elim _ _ }

end IteratedVirtual
end HeytingLean
