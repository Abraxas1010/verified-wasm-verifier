import Mathlib.Data.Set.Lattice
import HeytingLean.ATheory.Paper.AssemblySpace

namespace HeytingLean
namespace ATheory
namespace Paper

open scoped Classical

namespace AssemblySpace

variable (S : AssemblySpace)

/-- A single causal join step `(x, y, z)` equipped with evidence that the join is allowed. -/
structure Step where
  x : S.Ω
  y : S.Ω
  z : S.Ω
  ok : S.J x y z

/-- A step is usable given a set `A` of currently available objects when both inputs are in `A`. -/
def Step.usable (A : Set S.Ω) (s : Step S) : Prop := s.x ∈ A ∧ s.y ∈ A

/-- Well-formedness of a sequence of join steps, starting from primitives `U`.

At each step, you may use any previously available object (initially `U`), and the
output is added to the available set. This matches the paper’s sequential formulation
of an assembly path (and allows reuse of intermediate products by referencing them
multiple times as inputs).
-/
def WellFormedFrom : Set S.Ω → List (Step S) → Prop
  | _, [] => True
  | A, s :: ss => s.usable (S := S) A ∧ WellFormedFrom (Set.insert s.z A) ss

@[simp] lemma wellFormedFrom_nil (A : Set S.Ω) : WellFormedFrom (S := S) A [] := True.intro

/-- Compute the set of available objects after executing a step sequence starting from `A`. -/
def availableAfter : Set S.Ω → List (Step S) → Set S.Ω
  | A, [] => A
  | A, s :: ss => availableAfter (Set.insert s.z A) ss

@[simp] lemma availableAfter_nil (A : Set S.Ω) : availableAfter (S := S) A [] = A := rfl

lemma availableAfter_cons (A : Set S.Ω) (s : Step S) (ss : List (Step S)) :
    availableAfter (S := S) A (s :: ss) = availableAfter (S := S) (Set.insert s.z A) ss := rfl

lemma wellFormedFrom_append {A : Set S.Ω} {xs ys : List (Step S)}
    (hxs : WellFormedFrom (S := S) A xs)
    (hys : WellFormedFrom (S := S) (availableAfter (S := S) A xs) ys) :
    WellFormedFrom (S := S) A (xs ++ ys) := by
  induction xs generalizing A with
  | nil =>
      simpa [WellFormedFrom, availableAfter] using hys
  | cons s ss ih =>
      rcases hxs with ⟨hs, hss⟩
      have hys' : WellFormedFrom (S := S) (availableAfter (S := S) (Set.insert s.z A) ss) ys := by
        simpa [availableAfter] using hys
      exact And.intro hs (ih (A := Set.insert s.z A) (hxs := hss) (hys := hys'))

lemma wellFormedFrom_mono {A B : Set S.Ω} {xs : List (Step S)}
    (hAB : A ⊆ B) (hxs : WellFormedFrom (S := S) A xs) :
    WellFormedFrom (S := S) B xs := by
  induction xs generalizing A B with
  | nil => simp [WellFormedFrom]
  | cons s ss ih =>
      rcases hxs with ⟨hs, hss⟩
      have hs' : s.usable (S := S) B := ⟨hAB hs.1, hAB hs.2⟩
      have hAB' : Set.insert s.z A ⊆ Set.insert s.z B := by
        intro t ht
        rcases ht with rfl | ht
        · exact Or.inl rfl
        · exact Or.inr (hAB ht)
      exact And.intro hs' (ih (A := Set.insert s.z A) (B := Set.insert s.z B) hAB' hss)

lemma availableAfter_append (A : Set S.Ω) (xs ys : List (Step S)) :
    availableAfter (S := S) A (xs ++ ys) =
      availableAfter (S := S) (availableAfter (S := S) A xs) ys := by
  induction xs generalizing A with
  | nil => simp [availableAfter]
  | cons s ss ih =>
      simpa [availableAfter] using ih (A := Set.insert s.z A)

lemma subset_availableAfter (A : Set S.Ω) (xs : List (Step S)) :
    A ⊆ availableAfter (S := S) A xs := by
  induction xs generalizing A with
  | nil => simp [availableAfter]
  | cons s ss ih =>
      intro t ht
      have : t ∈ Set.insert s.z A := Or.inr ht
      simpa [availableAfter] using ih (A := Set.insert s.z A) this

lemma availableAfter_mono {A B : Set S.Ω} {xs : List (Step S)} (hAB : A ⊆ B) :
    availableAfter (S := S) A xs ⊆ availableAfter (S := S) B xs := by
  induction xs generalizing A B with
  | nil => simpa [availableAfter] using hAB
  | cons s ss ih =>
      have hAB' : Set.insert s.z A ⊆ Set.insert s.z B := by
        intro t ht
        rcases ht with rfl | ht
        · exact Or.inl rfl
        · exact Or.inr (hAB ht)
      simpa [availableAfter] using ih (A := Set.insert s.z A) (B := Set.insert s.z B) hAB'

lemma mem_availableAfter_of_getLast? {A : Set S.Ω} {steps : List (Step S)} {s : Step S}
    (hs : steps.getLast? = some s) : s.z ∈ availableAfter (S := S) A steps := by
  induction steps generalizing A with
  | nil =>
      simp at hs
  | cons t ts ih =>
      cases ts with
      | nil =>
          simp [List.getLast?] at hs
          cases hs
          exact Or.inl rfl
      | cons t2 ts2 =>
          have : (t2 :: ts2).getLast? = some s := by
            simpa [List.getLast?] using hs
          simpa [availableAfter] using ih (A := Set.insert t.z A) this

/-- A paper-style assembly path for `z`.

Either it is a primitive (`steps = []` and `z ∈ U`), or it is produced as the output of
a nonempty sequence of well-formed join steps.
-/
structure AssemblyPath (z : S.Ω) where
  steps : List (Step S)
  wf : WellFormedFrom (S := S) S.U steps
  ok_out :
    (steps = [] ∧ z ∈ S.U) ∨ (∃ s, steps.getLast? = some s ∧ s.z = z)

namespace AssemblyPath

variable {S}

def len {z : S.Ω} (p : AssemblyPath (S := S) z) : Nat := p.steps.length

@[simp] lemma len_mk {z : S.Ω} (steps) (wf) (ok_out) :
    len (p := (AssemblyPath.mk (S := S) (z := z) steps wf ok_out)) = steps.length := rfl

/-- The trivial path for a primitive object. -/
def primitive {z : S.Ω} (hz : z ∈ S.U) : AssemblyPath (S := S) z :=
  { steps := []
    wf := by simp [WellFormedFrom]
    ok_out := Or.inl ⟨rfl, hz⟩ }

@[simp] lemma primitive_len {z : S.Ω} (hz : z ∈ S.U) :
    (primitive (S := S) hz).len = 0 := rfl

lemma mem_availableAfter {z : S.Ω} (p : AssemblyPath (S := S) z) :
    z ∈ availableAfter (S := S) S.U p.steps := by
  rcases p.ok_out with ⟨hsteps, hz⟩ | hout
  · simpa [hsteps, availableAfter] using hz
  · rcases hout with ⟨s, hsLast, hsZ⟩
    subst hsZ
    exact mem_availableAfter_of_getLast? (S := S) (A := S.U) hsLast

end AssemblyPath

/-- Closure witness for the paper’s "Ω is the closure of U under J" condition:
every object in `Ω` has at least one assembly path.

This is packaged separately so one can talk about an abstract assembly space without
committing to the closure property.
-/
structure Closed (S : AssemblySpace) : Prop where
  exists_path : ∀ z : S.Ω, Nonempty (AssemblyPath (S := S) z)

end AssemblySpace

end Paper
end ATheory
end HeytingLean

