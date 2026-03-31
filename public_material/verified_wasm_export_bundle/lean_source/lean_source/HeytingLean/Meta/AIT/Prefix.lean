import Mathlib.Data.List.Basic

/-
# Prefix-free programs and code families (AIT core)

This module provides a minimal, constructive core for reasoning
about prefix-free programs and their lengths. It is designed as a
foundation for Occam-style theorems in an algorithmic information
theory (AIT) setting, and to be compatible with the existing
Occam and birth-index machinery in `HeytingLean.Epistemic.Occam`.

We intentionally keep the development small and self-contained:

* `Program` is represented as a bitstring (`List Bool`).
* `IsPrefix` is defined via concatenation.
* `PrefixFree` is a predicate on sets of programs.
* `codeLength` records the length of a program.

Later modules can build on this to introduce model classes,
democratic model voting, and links to birth index, without
modifying these core definitions.
-/

namespace HeytingLean.Meta.AIT

/-- A program is represented as a finite bitstring. -/
abbrev Program := List Bool

namespace Program

/-- The length of a program (number of bits). -/
def length (p : Program) : Nat :=
  List.length (p : List Bool)

@[simp] lemma length_nil : length ([] : Program) = 0 := by
  simp [length]

@[simp] lemma length_cons (b : Bool) (p : Program) :
    length (b :: p) = length p + 1 := by
  simp [length]

end Program

open Program

/-- `IsPrefix p q` means that `p` is a (possibly equal) prefix of `q`. -/
def IsPrefix (p q : Program) : Prop :=
  ∃ s : Program, p ++ s = q

namespace IsPrefix

@[simp] lemma refl (p : Program) : IsPrefix p p := by
  refine ⟨[], ?_⟩
  simp

lemma trans {p q r : Program} :
    IsPrefix p q → IsPrefix q r → IsPrefix p r := by
  intro h₁ h₂
  rcases h₁ with ⟨s₁, h₁⟩
  rcases h₂ with ⟨s₂, h₂⟩
  refine ⟨s₁ ++ s₂, ?_⟩
  calc
    p ++ (s₁ ++ s₂)
        = (p ++ s₁) ++ s₂ := by simp [List.append_assoc]
    _   = q ++ s₂ := by simp [h₁]
    _   = r := h₂

lemma length_le {p q : Program} :
    IsPrefix p q → Program.length p ≤ Program.length q := by
  intro h
  rcases h with ⟨s, hs⟩
  -- Work at the list level to avoid confusion about abbreviations.
  change List.length (p : List Bool) ≤ List.length (q : List Bool)
  have h₂ :
      List.length (p : List Bool) ≤
        List.length ((p : List Bool) ++ (s : List Bool)) := by
    simp [List.length_append]
  simpa [hs] using h₂

end IsPrefix

/-- A code family is prefix-free if no two distinct programs stand in
the prefix relation. Equal programs are allowed; what is forbidden
is a strict prefix relation between distinct elements. -/
def PrefixFree (C : Set Program) : Prop :=
  ∀ {p q : Program}, p ∈ C → q ∈ C → p ≠ q → ¬ IsPrefix p q

namespace PrefixFree

lemma symmetric {C : Set Program} (hC : PrefixFree C) :
    ∀ {p q : Program}, p ∈ C → q ∈ C → p ≠ q → ¬ IsPrefix q p := by
  intro p q hp hq hneq
  have := hC (p := q) (q := p) hq hp (ne_comm.mp hneq)
  exact this

lemma pair {C : Set Program} (hC : PrefixFree C)
    {p q : Program} (hp : p ∈ C) (hq : q ∈ C) (hneq : p ≠ q) :
    ¬ IsPrefix p q ∧ ¬ IsPrefix q p := by
  exact And.intro (hC hp hq hneq) (symmetric (C := C) hC hp hq hneq)

end PrefixFree

/-- Length of a program, exposed at the AIT level. -/
def codeLength (p : Program) : Nat :=
  Program.length p

@[simp] lemma codeLength_nil : codeLength ([] : Program) = 0 := by
  simp [codeLength, Program.length]

@[simp] lemma codeLength_cons (b : Bool) (p : Program) :
    codeLength (b :: p) = codeLength p + 1 := by
  simp [codeLength, Program.length_cons]

namespace Examples

/-- A simple finite code family containing a single program. -/
def C₁ : Set Program :=
  {p | p = [true]}

lemma C₁_prefixFree : PrefixFree C₁ := by
  intro p q hp hq hneq
  rcases hp with hp
  rcases hq with hq
  subst hp
  subst hq
  exact (hneq rfl).elim

end Examples

end HeytingLean.Meta.AIT
