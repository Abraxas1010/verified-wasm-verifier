import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Powerset

namespace HeytingLean.StackTheory

variable {Φ : Type*} [DecidableEq Φ] [Fintype Φ]

/-- Bennett §4: A program is a finite set of states. -/
abbrev Program (Φ : Type*) := Finset Φ

/-- Bennett §4: A vocabulary is a finite set of programs. -/
abbrev Vocabulary (Φ : Type*) [DecidableEq Φ] := Finset (Program Φ)

/-- Bennett §4: The truth set `T(l)` is the intersection of all programs in `l`. -/
def truthSet (l : Finset (Program Φ)) : Finset Φ :=
  Fintype.elems.filter (fun φ => ∀ p ∈ l, φ ∈ p)

@[simp]
theorem mem_truthSet {l : Finset (Program Φ)} {φ : Φ} :
    φ ∈ truthSet l ↔ φ ∈ Fintype.elems ∧ ∀ p ∈ l, φ ∈ p := by
  simp [truthSet]

/-- Bennett ESM Lemma 1 infrastructure: truth sets distribute across vocabulary union. -/
theorem truthSet_union (l₁ l₂ : Finset (Program Φ)) :
    truthSet (l₁ ∪ l₂) = truthSet l₁ ∩ truthSet l₂ := by
  ext φ
  constructor
  · intro h
    rcases mem_truthSet.mp h with ⟨hφ, hmem⟩
    refine Finset.mem_inter.mpr ?_
    constructor
    · exact mem_truthSet.mpr ⟨hφ, fun p hp => hmem p (Finset.mem_union.mpr (Or.inl hp))⟩
    · exact mem_truthSet.mpr ⟨hφ, fun p hp => hmem p (Finset.mem_union.mpr (Or.inr hp))⟩
  · intro h
    rcases Finset.mem_inter.mp h with ⟨h₁, h₂⟩
    rcases mem_truthSet.mp h₁ with ⟨hφ, hmem₁⟩
    rcases mem_truthSet.mp h₂ with ⟨_, hmem₂⟩
    exact mem_truthSet.mpr ⟨hφ, fun p hp =>
      match Finset.mem_union.mp hp with
      | Or.inl hp₁ => hmem₁ p hp₁
      | Or.inr hp₂ => hmem₂ p hp₂⟩

/-- Bennett §4: The truth set of the empty statement is the full state space. -/
theorem truthSet_empty :
    truthSet (∅ : Finset (Program Φ)) = Fintype.elems := by
  ext φ
  simp [truthSet]

end HeytingLean.StackTheory
