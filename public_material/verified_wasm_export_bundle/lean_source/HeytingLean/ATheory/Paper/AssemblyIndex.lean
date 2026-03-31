import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Lattice
import HeytingLean.ATheory.Paper.AssemblyPath
import HeytingLean.ATheory.AssemblyCore

namespace HeytingLean
namespace ATheory
namespace Paper

open scoped Classical

namespace AssemblySpace

variable (S : AssemblySpace)

namespace AssemblyIndex

def HasPathLen (z : S.Ω) (n : Nat) : Prop :=
  ∃ p : AssemblyPath (S := S) z, p.len = n

lemma exists_len_of_closed (hC : Closed S) (z : S.Ω) :
    ∃ n : Nat, HasPathLen (S := S) z n := by
  rcases hC.exists_path z with ⟨p⟩
  refine ⟨p.len, p, rfl⟩

noncomputable def assemblyIndex (hC : Closed S) (z : S.Ω) : Nat :=
  Nat.find (exists_len_of_closed (S := S) hC z)

lemma assemblyIndex_spec (hC : Closed S) (z : S.Ω) :
    HasPathLen (S := S) z (assemblyIndex (S := S) hC z) :=
  Nat.find_spec (exists_len_of_closed (S := S) hC z)

lemma assemblyIndex_le_of_hasLen (hC : Closed S) (z : S.Ω) {n : Nat}
    (hn : HasPathLen (S := S) z n) :
    assemblyIndex (S := S) hC z ≤ n :=
  Nat.find_min' (exists_len_of_closed (S := S) hC z) hn

lemma assemblyIndex_le_of_path (hC : Closed S) {z : S.Ω} (p : AssemblyPath (S := S) z) :
    assemblyIndex (S := S) hC z ≤ p.len :=
  assemblyIndex_le_of_hasLen (S := S) hC z ⟨p, rfl⟩

lemma assemblyIndex_eq_zero_iff (hC : Closed S) (z : S.Ω) :
    assemblyIndex (S := S) hC z = 0 ↔ z ∈ S.U := by
  constructor
  · intro hz
    rcases assemblyIndex_spec (S := S) hC z with ⟨p, hp⟩
    have hlen0 : p.len = 0 := by simpa [assemblyIndex] using hp.trans hz
    have : p.steps = [] := by
      exact (List.length_eq_zero_iff.mp (by simpa [AssemblyPath.len] using hlen0))
    rcases p.ok_out with ⟨hsteps, hzU⟩ | hout
    · simpa [this] using hzU
    · rcases hout with ⟨s, hsLast, _⟩
      simp [this] at hsLast
  · intro hzU
    have hn : HasPathLen (S := S) z 0 := by
      refine ⟨AssemblyPath.primitive (S := S) (z := z) hzU, ?_⟩
      rfl
    have hle : assemblyIndex (S := S) hC z ≤ 0 :=
      assemblyIndex_le_of_hasLen (S := S) hC z hn
    exact Nat.le_zero.mp hle

end AssemblyIndex

end AssemblySpace

/-! ## A concrete assembly space: syntax trees with a universal join operation -/

namespace ObjSyntax

open HeytingLean.ATheory

universe u

variable {Atom : Type u}

/-- Assembly space where objects are syntax trees `Obj Atom`, primitives are the base atoms,
and the join predicate is the universal constructor `join`.

This model is useful for sanity checks and for demonstrating how reuse can reduce
the assembly index below the raw `joinCount`.
-/
def space : Paper.AssemblySpace where
  Ω := Obj Atom
  U := {o | ∃ a, o = Obj.base a}
  J := fun x y z => z = Obj.join x y

namespace space

def primitive (a : Atom) : (space (Atom := Atom)).Ω := Obj.base a

@[simp] lemma mem_U_primitive (a : Atom) : primitive (Atom := Atom) a ∈ (space (Atom := Atom)).U :=
  ⟨a, rfl⟩

  open Paper.AssemblySpace

  private def canonicalSteps : Obj Atom → List (Step (space (Atom := Atom)))
  | Obj.base _ => []
  | Obj.join l r =>
      canonicalSteps l ++ canonicalSteps r ++
        [{ x := l, y := r, z := Obj.join l r, ok := rfl }]

private def canonicalPath : ∀ o : Obj Atom, AssemblyPath (S := space (Atom := Atom)) o
  | Obj.base a =>
      AssemblyPath.primitive (S := space (Atom := Atom)) (z := Obj.base a) (mem_U_primitive (Atom := Atom) a)
  | Obj.join l r => by
      classical
      let pL := canonicalPath l
      let pR := canonicalPath r
      have hUsub : (space (Atom := Atom)).U ⊆
          availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U pL.steps :=
        subset_availableAfter (S := space (Atom := Atom)) (A := (space (Atom := Atom)).U) pL.steps
      have wfR' : WellFormedFrom (S := space (Atom := Atom))
          (availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U pL.steps) pR.steps :=
        wellFormedFrom_mono (S := space (Atom := Atom)) (A := (space (Atom := Atom)).U)
          (B := availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U pL.steps)
          (xs := pR.steps) hUsub pR.wf
      have wfLR : WellFormedFrom (S := space (Atom := Atom)) (space (Atom := Atom)).U (pL.steps ++ pR.steps) :=
        wellFormedFrom_append (S := space (Atom := Atom)) (A := (space (Atom := Atom)).U)
          (xs := pL.steps) (ys := pR.steps) pL.wf (by
            simpa [availableAfter_append] using wfR')
      have hl : l ∈ availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U (pL.steps ++ pR.steps) := by
        have hl0 : l ∈ availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U pL.steps :=
          AssemblyPath.mem_availableAfter (S := space (Atom := Atom)) (z := l) pL
        have : l ∈ availableAfter (S := space (Atom := Atom))
            (availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U pL.steps) pR.steps :=
          (subset_availableAfter (S := space (Atom := Atom))
            (A := availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U pL.steps) pR.steps) hl0
        simpa [availableAfter_append] using (this : _)
      have hr : r ∈ availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U (pL.steps ++ pR.steps) := by
        have hr0 : r ∈ availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U pR.steps :=
          AssemblyPath.mem_availableAfter (S := space (Atom := Atom)) (z := r) pR
        have hUsub' : (space (Atom := Atom)).U ⊆
            availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U pL.steps :=
          subset_availableAfter (S := space (Atom := Atom)) (A := (space (Atom := Atom)).U) pL.steps
        have hr' : r ∈ availableAfter (S := space (Atom := Atom))
            (availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U pL.steps) pR.steps :=
          availableAfter_mono (S := space (Atom := Atom)) (A := (space (Atom := Atom)).U)
            (B := availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U pL.steps)
            (xs := pR.steps) hUsub' hr0
        simpa [availableAfter_append] using hr'

      let finalStep : Step (space (Atom := Atom)) := { x := l, y := r, z := Obj.join l r, ok := rfl }
      have wfFinal : WellFormedFrom (S := space (Atom := Atom))
          (availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U (pL.steps ++ pR.steps))
          [finalStep] := by
        simp [WellFormedFrom, Step.usable, hl, hr, finalStep]
      have wfAll : WellFormedFrom (S := space (Atom := Atom)) (space (Atom := Atom)).U (pL.steps ++ pR.steps ++ [finalStep]) := by
        exact wellFormedFrom_append (S := space (Atom := Atom)) (A := (space (Atom := Atom)).U)
          (xs := pL.steps ++ pR.steps) (ys := [finalStep]) wfLR (by simpa using wfFinal)
      exact
        { steps := pL.steps ++ pR.steps ++ [finalStep]
          wf := wfAll
          ok_out := by
            refine Or.inr ?_
            refine ⟨finalStep, ?_, rfl⟩
            simp }

  /-! ### Reuse-aware canonical path

  The paper-facing `assemblyIndex` minimizes path length under reuse. The simple
  `canonicalPath` above witnesses closure but it does not exploit reuse: it always
  builds `l` and `r` independently.

  The construction below tracks the set of currently available objects (as a `Set`)
  and skips any subtree that is already available.
  -/

  private noncomputable def reuseAwareSteps (A : Set (Obj Atom)) :
      Obj Atom → List (Step (space (Atom := Atom)))
    | Obj.base _ => []
    | Obj.join l r => by
        classical
        by_cases h : Obj.join l r ∈ A
        · exact []
        ·
          let stepsL := reuseAwareSteps A l
          let A1 := availableAfter (S := space (Atom := Atom)) A stepsL
          let stepsR := reuseAwareSteps A1 r
          let finalStep : Step (space (Atom := Atom)) := { x := l, y := r, z := Obj.join l r, ok := rfl }
          exact stepsL ++ stepsR ++ [finalStep]

  private lemma mem_availableAfter_of_mem_steps (A : Set (Obj Atom)) :
      ∀ {steps : List (Step (space (Atom := Atom)))} {s : Step (space (Atom := Atom))},
        s ∈ steps → s.z ∈ availableAfter (S := space (Atom := Atom)) A steps := by
    intro steps
    induction steps generalizing A with
    | nil =>
        intro s hs
        cases hs
    | cons t ts ih =>
        intro s hs
        cases hs with
        | head =>
            -- `s = t` (definitional) so `s.z = t.z` is immediately available.
            have : t.z ∈ Set.insert t.z A := Or.inl rfl
            have hA : Set.insert t.z A ⊆
                availableAfter (S := space (Atom := Atom)) (Set.insert t.z A) ts :=
              subset_availableAfter (S := space (Atom := Atom)) (A := Set.insert t.z A) ts
            simpa [availableAfter] using (hA this)
        | tail _ hsTail =>
            simpa [availableAfter] using (ih (A := Set.insert t.z A) (s := s) hsTail)

  private lemma reuseAwareSteps_z_not_mem (A : Set (Obj Atom)) :
      ∀ {o : Obj Atom} {s : Step (space (Atom := Atom))},
        s ∈ reuseAwareSteps (Atom := Atom) A o → s.z ∉ A := by
    intro o
    induction o generalizing A with
    | base a =>
        intro s hs
        simp [reuseAwareSteps] at hs
    | join l r ihL ihR =>
        classical
        intro s hs
        by_cases h : Obj.join l r ∈ A
        ·
          intro _
          have : False := by
            have hs0 := hs
            simp [reuseAwareSteps, h] at hs0
          exact this.elim
        ·
          simp [reuseAwareSteps, h] at hs
          rcases hs with hs | hs
          · exact ihL (A := A) hs
          · rcases hs with hs | hs
            ·
              -- `stepsR` is built with starting set `A1 = availableAfter A stepsL`.
              -- It outputs only elements not already in `A1`, hence not in `A`.
              let stepsL := reuseAwareSteps (Atom := Atom) A l
              let A1 := availableAfter (S := space (Atom := Atom)) A stepsL
              have hA : A ⊆ A1 := subset_availableAfter (S := space (Atom := Atom)) (A := A) stepsL
              have : s.z ∉ A1 := ihR (A := A1) hs
              intro hzA
              exact this (hA hzA)
            ·
              -- The final step output is the current join, which we assumed is not in `A`.
              rcases hs with rfl
              simpa using h

  private lemma reuseAwareSteps_wf (A : Set (Obj Atom))
      (hU : (space (Atom := Atom)).U ⊆ A) :
      ∀ o : Obj Atom,
        WellFormedFrom (S := space (Atom := Atom)) A (reuseAwareSteps (Atom := Atom) A o) := by
    -- First show that the construction always makes its target available.
    have makes_available :
        ∀ (A : Set (Obj Atom))
          (hU : (space (Atom := Atom)).U ⊆ A) (o : Obj Atom),
          o ∈
            availableAfter (S := space (Atom := Atom)) A (reuseAwareSteps (Atom := Atom) A o) := by
      intro A hU o
      induction o generalizing A with
      | base a =>
          have hU' : Obj.base a ∈ (space (Atom := Atom)).U := ⟨a, rfl⟩
          simpa [reuseAwareSteps] using hU hU'
      | join l r ihL ihR =>
          classical
          by_cases h : Obj.join l r ∈ A
          ·
            simp [reuseAwareSteps, h]
          ·
            let stepsL := reuseAwareSteps (Atom := Atom) A l
            let A1 := availableAfter (S := space (Atom := Atom)) A stepsL
            let stepsR := reuseAwareSteps (Atom := Atom) A1 r
            let finalStep : Step (space (Atom := Atom)) := { x := l, y := r, z := Obj.join l r, ok := rfl }
            have hU1 : (space (Atom := Atom)).U ⊆ A1 := by
              intro x hx
              exact (subset_availableAfter (S := space (Atom := Atom)) (A := A) stepsL) (hU hx)
            have : Obj.join l r ∈
                availableAfter (S := space (Atom := Atom))
                  (availableAfter (S := space (Atom := Atom)) A (stepsL ++ stepsR)) [finalStep] := by
              -- After the singleton step, its output is inserted into the available set.
              change Obj.join l r ∈
                Set.insert (Obj.join l r)
                  (availableAfter (S := space (Atom := Atom)) A (stepsL ++ stepsR))
              exact Or.inl rfl
            -- Rewrite the nested `availableAfter` into the concrete concatenation shape.
            simpa [reuseAwareSteps, h, stepsL, stepsR, finalStep, A1, List.append_assoc,
              availableAfter_append] using this

    intro o
    induction o generalizing A with
    | base a =>
        simp [reuseAwareSteps]
    | join l r ihL ihR =>
        classical
        by_cases h : Obj.join l r ∈ A
        · simp [reuseAwareSteps, h]
        ·
          let stepsL := reuseAwareSteps (Atom := Atom) A l
          let A1 := availableAfter (S := space (Atom := Atom)) A stepsL
          let stepsR := reuseAwareSteps (Atom := Atom) A1 r
          let finalStep : Step (space (Atom := Atom)) := { x := l, y := r, z := Obj.join l r, ok := rfl }
          have wfL : WellFormedFrom (S := space (Atom := Atom)) A stepsL :=
            ihL (A := A) (hU := hU)
          have hU1 : (space (Atom := Atom)).U ⊆ A1 := by
            intro x hx
            exact (subset_availableAfter (S := space (Atom := Atom)) (A := A) stepsL) (hU hx)
          have wfR : WellFormedFrom (S := space (Atom := Atom)) A1 stepsR :=
            ihR (A := A1) (hU := hU1)
          have wfLR : WellFormedFrom (S := space (Atom := Atom)) A (stepsL ++ stepsR) := by
            refine wellFormedFrom_append (S := space (Atom := Atom)) (A := A)
              (xs := stepsL) (ys := stepsR) wfL ?_
            simpa [A1] using wfR
          have hl0 : l ∈ availableAfter (S := space (Atom := Atom)) A stepsL := by
            simpa [stepsL] using makes_available (A := A) (hU := hU) l
          have hr0 : r ∈ availableAfter (S := space (Atom := Atom)) A1 stepsR := by
            simpa [stepsR] using makes_available (A := A1) (hU := hU1) r
          have hl : l ∈ availableAfter (S := space (Atom := Atom)) A (stepsL ++ stepsR) := by
            have : l ∈
                availableAfter (S := space (Atom := Atom))
                  (availableAfter (S := space (Atom := Atom)) A stepsL) stepsR :=
              (subset_availableAfter (S := space (Atom := Atom))
                (A := availableAfter (S := space (Atom := Atom)) A stepsL) stepsR) hl0
            simpa [availableAfter_append, A1] using this
          have hr : r ∈ availableAfter (S := space (Atom := Atom)) A (stepsL ++ stepsR) := by
            -- Rewrite `availableAfter A (stepsL ++ stepsR)` into `availableAfter A1 stepsR`.
            simpa [availableAfter_append, A1] using hr0
          have wfFinal : WellFormedFrom (S := space (Atom := Atom))
              (availableAfter (S := space (Atom := Atom)) A (stepsL ++ stepsR)) [finalStep] := by
            simp [WellFormedFrom, Step.usable, hl, hr, finalStep]
          have wfAll : WellFormedFrom (S := space (Atom := Atom)) A (stepsL ++ stepsR ++ [finalStep]) := by
            exact wellFormedFrom_append (S := space (Atom := Atom)) (A := A)
              (xs := stepsL ++ stepsR) (ys := [finalStep]) wfLR (by simpa using wfFinal)
          simpa [reuseAwareSteps, h, stepsL, stepsR, finalStep, List.append_assoc] using wfAll

  /-- A reuse-aware path for `o`, starting from primitives `U`. -/
  private noncomputable def reuseAwarePath : ∀ o : Obj Atom,
      AssemblyPath (S := space (Atom := Atom)) o
    | Obj.base a =>
        AssemblyPath.primitive (S := space (Atom := Atom)) (z := Obj.base a) (mem_U_primitive (Atom := Atom) a)
    | Obj.join l r => by
        classical
        let steps := reuseAwareSteps (Atom := Atom) (space (Atom := Atom)).U (Obj.join l r)
        have wf : WellFormedFrom (S := space (Atom := Atom)) (space (Atom := Atom)).U steps := by
          simpa [steps] using reuseAwareSteps_wf (Atom := Atom)
            (A := (space (Atom := Atom)).U) (hU := subset_rfl) (o := Obj.join l r)
        -- The last step is the final join producing the target.
        refine
          { steps := steps
            wf := wf
            ok_out := Or.inr ?_ }
        -- Unfold one step so `simp` can see the final `++ [finalStep]` shape.
        have hNot : Obj.join l r ∉ (space (Atom := Atom)).U := by
          intro hmem
          rcases hmem with ⟨a, ha⟩
          cases ha
        simp [steps, reuseAwareSteps, hNot]

  private lemma joinCount_le_of_mem_subobjects [DecidableEq Atom] :
      ∀ {o t : Obj Atom}, t ∈ Obj.subobjects o → Obj.joinCount t ≤ Obj.joinCount o := by
    intro o
    induction o with
    | base a =>
        intro t ht
        simp [Obj.subobjects] at ht
        subst ht
        simp [Obj.joinCount]
    | join l r ihL ihR =>
        intro t ht
        simp [Obj.subobjects] at ht
        rcases ht with rfl | ht
        · simp [Obj.joinCount]
        ·
          cases ht with
          | inl hl =>
              have hle : Obj.joinCount t ≤ Obj.joinCount l := ihL hl
              have : Obj.joinCount t ≤ Obj.joinCount l + Obj.joinCount r + 1 := by
                calc
                  Obj.joinCount t ≤ Obj.joinCount l := hle
                  _ ≤ Obj.joinCount l + Obj.joinCount r := Nat.le_add_right _ _
                  _ ≤ Obj.joinCount l + Obj.joinCount r + 1 := Nat.le_add_right _ _
              simpa [Obj.joinCount] using this
          | inr hr =>
              have hle : Obj.joinCount t ≤ Obj.joinCount r := ihR hr
              have : Obj.joinCount t ≤ Obj.joinCount l + Obj.joinCount r + 1 := by
                calc
                  Obj.joinCount t ≤ Obj.joinCount r := hle
                  _ ≤ Obj.joinCount l + Obj.joinCount r := Nat.le_add_left _ _
                  _ ≤ Obj.joinCount l + Obj.joinCount r + 1 := Nat.le_add_right _ _
              simpa [Obj.joinCount] using this

  private lemma join_not_mem_subobjects_left [DecidableEq Atom] (l r : Obj Atom) :
      Obj.join l r ∉ Obj.subobjects l := by
    intro hmem
    have hle : Obj.joinCount (Obj.join l r) ≤ Obj.joinCount l :=
      joinCount_le_of_mem_subobjects (Atom := Atom) (o := l) (t := Obj.join l r) hmem
    have hgt : Obj.joinCount (Obj.join l r) > Obj.joinCount l := by
      simp [Obj.joinCount, Nat.add_assoc]
    exact (Nat.not_le_of_gt hgt) hle

  private lemma join_not_mem_subobjects_right [DecidableEq Atom] (l r : Obj Atom) :
      Obj.join l r ∉ Obj.subobjects r := by
    intro hmem
    have hle : Obj.joinCount (Obj.join l r) ≤ Obj.joinCount r :=
      joinCount_le_of_mem_subobjects (Atom := Atom) (o := r) (t := Obj.join l r) hmem
    have hgt : Obj.joinCount (Obj.join l r) > Obj.joinCount r := by
      have hpos : 0 < Obj.joinCount l + 1 := Nat.succ_pos _
      have hlt : Obj.joinCount r < Obj.joinCount r + (Obj.joinCount l + 1) :=
        Nat.lt_add_of_pos_right (n := Obj.joinCount r) (k := Obj.joinCount l + 1) hpos
      -- Commute the sum into `joinCount l + joinCount r + 1`.
      simpa [Obj.joinCount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlt
    exact (Nat.not_le_of_gt hgt) hle

  private lemma reuseAwareSteps_z_mem_subobjects [DecidableEq Atom] (A : Set (Obj Atom)) :
      ∀ {o : Obj Atom} {s : Step (space (Atom := Atom))},
        s ∈ reuseAwareSteps (Atom := Atom) A o → s.z ∈ Obj.subobjects o := by
    intro o
    induction o generalizing A with
    | base a =>
        intro s hs
        simp [reuseAwareSteps] at hs
    | join l r ihL ihR =>
        classical
        haveI : DecidableEq (Obj Atom) := fun a b => instDecidableEqObj a b
        intro s hs
        by_cases h : Obj.join l r ∈ A
        ·
          have hs0 := hs
          simp [reuseAwareSteps, h] at hs0
        ·
          let stepsL := reuseAwareSteps (Atom := Atom) A l
          let A1 := availableAfter (S := space (Atom := Atom)) A stepsL
          let stepsR := reuseAwareSteps (Atom := Atom) A1 r
          let finalStep : Step (space (Atom := Atom)) := { x := l, y := r, z := Obj.join l r, ok := rfl }
          have hs' : s ∈ stepsL ++ stepsR ++ [finalStep] := by
            simpa [reuseAwareSteps, h, stepsL, A1, stepsR, finalStep, List.append_assoc] using hs
          have hs'' : s ∈ stepsL ++ stepsR ∨ s ∈ [finalStep] := by
            simpa [List.append_assoc] using (List.mem_append.mp hs')
          rcases hs'' with hsLR | hsF
          ·
            have hsLR' : s ∈ stepsL ∨ s ∈ stepsR := by
              simpa using (List.mem_append.mp hsLR)
            cases hsLR' with
            | inl hsL =>
                have hz : s.z ∈ Obj.subobjects l := ihL (A := A) hsL
                -- Unfold `subobjects` of the join and discharge by simp.
                simp [Obj.subobjects, hz]
            | inr hsR =>
                have hz : s.z ∈ Obj.subobjects r := ihR (A := A1) hsR
                simp [Obj.subobjects, hz]
          ·
            have : s = finalStep := by simpa using hsF
            subst this
            simp [finalStep, Obj.subobjects]

  private lemma reuseAwareSteps_z_isJoin (A : Set (Obj Atom)) :
      ∀ {o : Obj Atom} {s : Step (space (Atom := Atom))},
        s ∈ reuseAwareSteps (Atom := Atom) A o → Obj.isJoin s.z = true := by
    intro o
    induction o generalizing A with
    | base a =>
        intro s hs
        simp [reuseAwareSteps] at hs
    | join l r ihL ihR =>
        classical
        intro s hs
        by_cases h : Obj.join l r ∈ A
        ·
          have hs0 := hs
          simp [reuseAwareSteps, h] at hs0
        ·
          let stepsL := reuseAwareSteps (Atom := Atom) A l
          let A1 := availableAfter (S := space (Atom := Atom)) A stepsL
          let stepsR := reuseAwareSteps (Atom := Atom) A1 r
          let finalStep : Step (space (Atom := Atom)) := { x := l, y := r, z := Obj.join l r, ok := rfl }
          have hs' : s ∈ stepsL ++ stepsR ++ [finalStep] := by
            simpa [reuseAwareSteps, h, stepsL, A1, stepsR, finalStep, List.append_assoc] using hs
          have hs'' : s ∈ stepsL ++ stepsR ∨ s ∈ [finalStep] := by
            simpa [List.append_assoc] using (List.mem_append.mp hs')
          rcases hs'' with hsLR | hsF
          ·
            have hsLR' : s ∈ stepsL ∨ s ∈ stepsR := by
              simpa using (List.mem_append.mp hsLR)
            cases hsLR' with
            | inl hsL => exact ihL (A := A) hsL
            | inr hsR => exact ihR (A := A1) hsR
          ·
            have : s = finalStep := by simpa using hsF
            subst this
            simp [Obj.isJoin, finalStep]

  private lemma reuseAwareSteps_nodup_z [DecidableEq Atom] (A : Set (Obj Atom)) :
      ∀ o : Obj Atom, (reuseAwareSteps (Atom := Atom) A o |>.map (fun s => s.z)).Nodup := by
    intro o
    induction o generalizing A with
    | base a => simp [reuseAwareSteps]
    | join l r ihL ihR =>
        classical
        haveI : DecidableEq (Obj Atom) := fun a b => instDecidableEqObj a b
        by_cases h : Obj.join l r ∈ A
        · simp [reuseAwareSteps, h]
        ·
          let stepsL := reuseAwareSteps (Atom := Atom) A l
          let A1 := availableAfter (S := space (Atom := Atom)) A stepsL
          let stepsR := reuseAwareSteps (Atom := Atom) A1 r
          let finalStep : Step (space (Atom := Atom)) := { x := l, y := r, z := Obj.join l r, ok := rfl }
          let zOut : Step (space (Atom := Atom)) → Obj Atom := fun s => s.z
          have hL : (stepsL.map zOut).Nodup := ihL (A := A)
          have hR : (stepsR.map zOut).Nodup := ihR (A := A1)
          have hNoCommon :
              ∀ a ∈ stepsL.map zOut, ∀ b ∈ stepsR.map zOut, a ≠ b := by
            intro a ha b hb hab
            rcases List.mem_map.mp ha with ⟨sa, hsa, rfl⟩
            rcases List.mem_map.mp hb with ⟨sb, hsb, rfl⟩
            have haA1 : sa.z ∈ A1 := by
              simpa [A1, stepsL] using
                (mem_availableAfter_of_mem_steps (Atom := Atom) (A := A) (steps := stepsL) (s := sa) hsa)
            have hbNot : sb.z ∉ A1 := by
              simpa [stepsR] using
                (reuseAwareSteps_z_not_mem (Atom := Atom) (A := A1) (o := r) hsb)
            have hab' : sa.z = sb.z := by
              simpa [eq_comm, zOut] using hab
            have hbA1 : sb.z ∈ A1 := by
              simpa [hab'] using haA1
            exact hbNot hbA1
          have hLR :
              ((stepsL.map zOut) ++ (stepsR.map zOut)).Nodup := by
            exact (List.nodup_append).2 ⟨hL, hR, hNoCommon⟩
          have hJoinNot : Obj.join l r ∉ (stepsL.map zOut ++ stepsR.map zOut) := by
            intro hmem
            have hmem' : Obj.join l r ∈ stepsL.map zOut ∨ Obj.join l r ∈ stepsR.map zOut :=
              List.mem_append.mp hmem
            rcases hmem' with hLmem | hRmem
            ·
              rcases List.mem_map.mp hLmem with ⟨s, hs, hsZ⟩
              have hzSub0 : s.z ∈ Obj.subobjects l :=
                reuseAwareSteps_z_mem_subobjects (Atom := Atom) (A := A) (o := l) hs
              have hsZ' : s.z = Obj.join l r := by
                simpa [zOut] using hsZ
              have hzSub : Obj.join l r ∈ Obj.subobjects l := by
                simpa [hsZ'] using hzSub0
              exact join_not_mem_subobjects_left (Atom := Atom) l r hzSub
            ·
              rcases List.mem_map.mp hRmem with ⟨s, hs, hsZ⟩
              have hzSub0 : s.z ∈ Obj.subobjects r :=
                reuseAwareSteps_z_mem_subobjects (Atom := Atom) (A := A1) (o := r) hs
              have hsZ' : s.z = Obj.join l r := by
                simpa [zOut] using hsZ
              have hzSub : Obj.join l r ∈ Obj.subobjects r := by
                simpa [hsZ'] using hzSub0
              exact join_not_mem_subobjects_right (Atom := Atom) l r hzSub
          have hAll :
              (stepsL.map zOut ++ stepsR.map zOut ++ [Obj.join l r]).Nodup := by
            -- Use `nodup_append` again, with `l₂ = [join l r]`.
            have hLast : [Obj.join l r].Nodup := by simp
            have hNoLast :
                ∀ a ∈ (stepsL.map zOut ++ stepsR.map zOut),
                  ∀ b ∈ [Obj.join l r], a ≠ b := by
              intro a ha b hb hab
              have : b = Obj.join l r := by simpa using hb
              subst this
              exact hJoinNot (by simpa [hab] using ha)
            exact (List.nodup_append).2 ⟨hLR, hLast, hNoLast⟩
          simpa [reuseAwareSteps, h, stepsL, A1, stepsR, finalStep, zOut, List.map_append, List.append_assoc] using hAll

  private lemma reuseAwareSteps_len_le_dagJoinCount [DecidableEq Atom] (o : Obj Atom) :
      (reuseAwareSteps (Atom := Atom) (space (Atom := Atom)).U o).length ≤ Obj.dagJoinCount o := by
    classical
    let steps := reuseAwareSteps (Atom := Atom) (space (Atom := Atom)).U o
    let outs := steps.map (fun s => s.z)
    have hNodup : outs.Nodup := by
      simpa [steps, outs] using reuseAwareSteps_nodup_z (Atom := Atom) (A := (space (Atom := Atom)).U) o
    have hSubset : outs.toFinset ⊆ (Obj.subobjects o).filter (fun t => Obj.isJoin t) := by
      intro t ht
      have ht' : t ∈ outs := by
        simpa using (List.mem_toFinset.mp ht)
      rcases List.mem_map.mp ht' with ⟨s, hs, rfl⟩
      have hzSub : s.z ∈ Obj.subobjects o := by
        simpa [steps, outs] using
          reuseAwareSteps_z_mem_subobjects (Atom := Atom) (A := (space (Atom := Atom)).U) (o := o) hs
      have hzJoin : Obj.isJoin s.z = true := by
        simpa [steps, outs] using
          reuseAwareSteps_z_isJoin (Atom := Atom) (A := (space (Atom := Atom)).U) (o := o) hs
      simp [Finset.mem_filter, hzSub, hzJoin]
    have hCard : outs.toFinset.card ≤ ((Obj.subobjects o).filter (fun t => Obj.isJoin t)).card :=
      Finset.card_le_card hSubset
    have hOutsCard : outs.toFinset.card = outs.length :=
      List.toFinset_card_of_nodup hNodup
    have : steps.length ≤ ((Obj.subobjects o).filter (fun t => Obj.isJoin t)).card := by
      -- `steps.length = outs.length` and `outs.length = outs.toFinset.card` (nodup).
      have hLen : steps.length = outs.length := by
        simp [outs]
      -- Convert `outs.toFinset.card ≤ ...` into a length bound.
      have : outs.length ≤ ((Obj.subobjects o).filter (fun t => Obj.isJoin t)).card := by
        simpa [hOutsCard] using hCard
      exact hLen.le.trans this
    simpa [Obj.dagJoinCount, steps] using this

  lemma closed : Closed (space (Atom := Atom)) := by
    refine ⟨fun z => ?_⟩
    exact ⟨canonicalPath (Atom := Atom) z⟩

  lemma assemblyIndex_le_joinCount (o : Obj Atom) :
      AssemblyIndex.assemblyIndex (S := space (Atom := Atom)) (hC := closed (Atom := Atom)) o ≤ Obj.joinCount o := by
  have hlen : (canonicalPath (Atom := Atom) o).len = Obj.joinCount o := by
    induction o with
    | base _ => simp [canonicalPath, Obj.joinCount]
    | join l r ihL ihR =>
        have ihL' : (canonicalPath (Atom := Atom) l).steps.length = Obj.joinCount l := by
          simpa [AssemblyPath.len] using ihL
        have ihR' : (canonicalPath (Atom := Atom) r).steps.length = Obj.joinCount r := by
          simpa [AssemblyPath.len] using ihR
        simp [canonicalPath, Obj.joinCount, AssemblyPath.len, List.length_append, ihL', ihR',
          Nat.add_left_comm, Nat.add_comm]
  have := AssemblyIndex.assemblyIndex_le_of_path
    (S := space (Atom := Atom)) (hC := closed (Atom := Atom)) (z := o) (canonicalPath (Atom := Atom) o)
  simpa [hlen] using this

  lemma assemblyIndex_le_dagJoinCount [DecidableEq Atom] (o : Obj Atom) :
      AssemblyIndex.assemblyIndex (S := space (Atom := Atom)) (hC := closed (Atom := Atom)) o ≤
        Obj.dagJoinCount o := by
    classical
    -- Use the explicit reuse-aware witness path.
    let p := reuseAwarePath (Atom := Atom) o
    have hmin :
        AssemblyIndex.assemblyIndex (S := space (Atom := Atom)) (hC := closed (Atom := Atom)) o ≤ p.len :=
      AssemblyIndex.assemblyIndex_le_of_path
        (S := space (Atom := Atom)) (hC := closed (Atom := Atom)) (z := o) p
    have hbound : p.len ≤ Obj.dagJoinCount o := by
      cases o with
      | base a =>
          -- `p` is the primitive path, so `p.len = 0`.
          have : p.len = 0 := by
            simp [p, reuseAwarePath]
          -- Any card is ≥ 0.
          simp [this]
      | join l r =>
          -- `p.steps` is `reuseAwareSteps U (join l r)`.
          simpa [p, reuseAwarePath, AssemblyPath.len] using
            (reuseAwareSteps_len_le_dagJoinCount (Atom := Atom) (o := Obj.join l r))
    exact le_trans hmin hbound

  /-! ### Equality for the syntax-tree model

  In `ObjSyntax.space`, the only way to produce a `join` object is to execute a step
  whose output is exactly that join. Since every join-subobject of `o` must be
  produced at least once in any path that builds `o`, we get the reverse inequality
  `Obj.dagJoinCount o ≤ assemblyIndex o` and hence equality.
  -/

  private lemma join_not_mem_U (t : Obj Atom) (htJoin : Obj.isJoin t = true) :
      t ∉ (space (Atom := Atom)).U := by
    cases t with
    | base a =>
        simp [Obj.isJoin] at htJoin
    | join l r =>
        intro hmem
        rcases hmem with ⟨a, ha⟩
        cases ha

  private lemma exists_step_of_mem_availableAfter {A : Set (Obj Atom)} :
      ∀ {steps : List (Step (space (Atom := Atom)))} {u : Obj Atom},
        u ∈ availableAfter (S := space (Atom := Atom)) A steps →
        u ∉ A →
        ∃ s ∈ steps, s.z = u := by
    intro steps
    induction steps generalizing A with
    | nil =>
        intro u hu hnot
        simpa [availableAfter] using (hnot hu)
    | cons t ts ih =>
        intro u hu hnot
        have hu' : u ∈ availableAfter (S := space (Atom := Atom)) (Set.insert t.z A) ts := by
          simpa [availableAfter] using hu
        by_cases hEq : u = t.z
        · refine ⟨t, by simp, by simp [hEq]⟩
        ·
          have hnot' : u ∉ Set.insert t.z A := by
            intro huins
            rcases huins with rfl | huA
            · exact hEq rfl
            · exact hnot huA
          rcases ih (A := Set.insert t.z A) (u := u) hu' hnot' with ⟨s, hs, hsz⟩
          refine ⟨s, ?_, hsz⟩
          exact List.mem_cons_of_mem _ hs

  private lemma step_inputs_mem_availableAfter {A : Set (Obj Atom)}
      {steps : List (Step (space (Atom := Atom)))}
      (wf : WellFormedFrom (S := space (Atom := Atom)) A steps) :
      ∀ {s : Step (space (Atom := Atom))}, s ∈ steps →
        s.x ∈ availableAfter (S := space (Atom := Atom)) A steps ∧
        s.y ∈ availableAfter (S := space (Atom := Atom)) A steps := by
    intro s hs
    induction steps generalizing A with
    | nil =>
        cases hs
    | cons t ts ih =>
        rcases wf with ⟨htUse, wfTail⟩
        cases hs with
        | head =>
            have hsub : A ⊆ availableAfter (S := space (Atom := Atom)) A (s :: ts) :=
              subset_availableAfter (S := space (Atom := Atom)) (A := A) (s :: ts)
            exact ⟨hsub htUse.1, hsub htUse.2⟩
        | tail _ hsTail =>
            have hxy : s.x ∈ availableAfter (S := space (Atom := Atom)) (Set.insert t.z A) ts ∧
                s.y ∈ availableAfter (S := space (Atom := Atom)) (Set.insert t.z A) ts :=
              ih (A := Set.insert t.z A) (wf := wfTail) hsTail
            simpa [availableAfter] using hxy

  private lemma join_components_mem_availableAfter
      [DecidableEq Atom]
      {steps : List (Step (space (Atom := Atom)))}
      (wf : WellFormedFrom (S := space (Atom := Atom)) (space (Atom := Atom)).U steps)
      (l r : Obj Atom)
      (hjr : Obj.join l r ∈ availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U steps) :
      l ∈ availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U steps ∧
      r ∈ availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U steps := by
    have hnotU : Obj.join l r ∉ (space (Atom := Atom)).U :=
      join_not_mem_U (Atom := Atom) (t := Obj.join l r) (by simp [Obj.isJoin])
    rcases
        exists_step_of_mem_availableAfter (Atom := Atom)
          (A := (space (Atom := Atom)).U) (steps := steps) (u := Obj.join l r) hjr hnotU with
      ⟨s, hs, hsz⟩
    have hxy := step_inputs_mem_availableAfter (Atom := Atom)
      (A := (space (Atom := Atom)).U) (steps := steps) wf (s := s) hs
    have hjoin : Obj.join s.x s.y = Obj.join l r := by
      -- `s.ok : s.z = join s.x s.y` and `hsz : s.z = join l r`.
      calc
        Obj.join s.x s.y = s.z := by
          symm
          exact s.ok
        _ = Obj.join l r := hsz
    have hxhy : s.x = l ∧ s.y = r := by
      injection hjoin with hx hy
      exact ⟨hx, hy⟩
    refine ⟨?_, ?_⟩
    · simpa [hxhy.1] using hxy.1
    · simpa [hxhy.2] using hxy.2

  private lemma subobjects_mem_availableAfter_of_mem
      [DecidableEq Atom]
      {steps : List (Step (space (Atom := Atom)))}
      (wf : WellFormedFrom (S := space (Atom := Atom)) (space (Atom := Atom)).U steps) :
      ∀ {u : Obj Atom}, u ∈ availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U steps →
        ∀ {t : Obj Atom}, t ∈ Obj.subobjects u →
          t ∈ availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U steps := by
    intro u hu t ht
    induction u with
    | base a =>
        simp [Obj.subobjects] at ht
        subst ht
        have hU : Obj.base a ∈ (space (Atom := Atom)).U := ⟨a, rfl⟩
        exact (subset_availableAfter (S := space (Atom := Atom)) (A := (space (Atom := Atom)).U) steps) hU
    | join l r ihL ihR =>
        have hlr :
            l ∈ availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U steps ∧
              r ∈ availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U steps :=
          join_components_mem_availableAfter (Atom := Atom) (steps := steps) wf l r hu
        simp [Obj.subobjects] at ht
        rcases ht with rfl | ht
        · exact hu
        ·
          have ht' : t ∈ Obj.subobjects l ∨ t ∈ Obj.subobjects r := by
            simpa [Finset.mem_union] using ht
          cases ht' with
          | inl htl => exact ihL (hu := hlr.1) htl
          | inr htr => exact ihR (hu := hlr.2) htr

  private lemma join_subobj_mem_step_outputs
      [DecidableEq Atom]
      {o : Obj Atom}
      (p : AssemblyPath (S := space (Atom := Atom)) o)
      (t : Obj Atom)
      (ht : t ∈ Obj.subobjects o)
      (htJoin : Obj.isJoin t = true) :
      ∃ s ∈ p.steps, s.z = t := by
    have ho : o ∈ availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U p.steps :=
      AssemblyPath.mem_availableAfter (S := space (Atom := Atom)) (z := o) p
    have htAvail : t ∈ availableAfter (S := space (Atom := Atom)) (space (Atom := Atom)).U p.steps :=
      subobjects_mem_availableAfter_of_mem (Atom := Atom) (steps := p.steps) p.wf ho (t := t) ht
    have htNotU : t ∉ (space (Atom := Atom)).U := join_not_mem_U (Atom := Atom) t htJoin
    exact
      exists_step_of_mem_availableAfter (Atom := Atom)
        (A := (space (Atom := Atom)).U) (steps := p.steps) (u := t) htAvail htNotU

  private lemma dagJoinCount_le_path_len
      [DecidableEq Atom]
      {o : Obj Atom}
      (p : AssemblyPath (S := space (Atom := Atom)) o) :
      Obj.dagJoinCount o ≤ p.len := by
    classical
    let joins : Finset (Obj Atom) := (Obj.subobjects o).filter (fun t => Obj.isJoin t)
    let outs : List (Obj Atom) := p.steps.map (fun s => s.z)
    have hsubset : joins ⊆ outs.toFinset := by
      intro t ht
      have htSub : t ∈ Obj.subobjects o := (Finset.mem_filter.mp ht).1
      have htJoin : Obj.isJoin t = true := (Finset.mem_filter.mp ht).2
      rcases join_subobj_mem_step_outputs (Atom := Atom) (o := o) p t htSub htJoin with ⟨s, hs, hsz⟩
      have hmemOuts : t ∈ outs := by
        have : ∃ a, a ∈ p.steps ∧ (fun s => s.z) a = t :=
          ⟨s, hs, by simpa using hsz⟩
        simpa [outs] using (List.mem_map).2 this
      exact (List.mem_toFinset).2 hmemOuts
    have hcard1 : joins.card ≤ outs.toFinset.card :=
      Finset.card_le_card hsubset
    have hcard2 : outs.toFinset.card ≤ outs.length :=
      List.toFinset_card_le outs
    have : joins.card ≤ p.len := by
      have : joins.card ≤ outs.length := le_trans hcard1 hcard2
      simpa [joins, outs, AssemblyPath.len] using this
    simpa [Obj.dagJoinCount, joins] using this

  lemma assemblyIndex_eq_dagJoinCount [DecidableEq Atom] (o : Obj Atom) :
      AssemblyIndex.assemblyIndex (S := space (Atom := Atom)) (hC := closed (Atom := Atom)) o =
        Obj.dagJoinCount o := by
    classical
    apply Nat.le_antisymm
    · exact assemblyIndex_le_dagJoinCount (Atom := Atom) (o := o)
    ·
      rcases
          AssemblyIndex.assemblyIndex_spec
            (S := space (Atom := Atom)) (hC := closed (Atom := Atom)) o with
        ⟨p, hp⟩
      have hbound : Obj.dagJoinCount o ≤ p.len :=
        dagJoinCount_le_path_len (Atom := Atom) (o := o) p
      simpa [hp] using hbound



end space

end ObjSyntax

end Paper
end ATheory
end HeytingLean
