import HeytingLean.Quantum.OML.Core

open scoped Classical

namespace HeytingLean.Quantum.OML

instance : OrthocomplementedLattice Prop where
  compl := Not
  involutive := by intro a; by_cases a <;> simp [*]
  antitone := by
    intro a b h -- h : a → b; need: (¬ b) → (¬ a)
    intro hb ha; exact hb (h ha)
  inf_compl := by intro a; by_cases a <;> simp [*]
  sup_compl := by intro a; by_cases a <;> simp [*]

instance : OrthomodularLattice Prop where
  toOrthocomplementedLattice := (inferInstance : OrthocomplementedLattice Prop)
  orthomodular := by
    intro a b h
    -- show: b = a ∨ (¬ a ∧ b)
    apply propext; constructor
    · intro hb; by_cases ha : a <;> simp [ha, hb]
    · intro hright; rcases hright with hleft | ⟨hna, hb⟩
      · exact h hleft
      · exact hb

end HeytingLean.Quantum.OML

