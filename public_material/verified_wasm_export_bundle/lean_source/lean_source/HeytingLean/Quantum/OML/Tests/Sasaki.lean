import HeytingLean.Quantum.OML.Sasaki

open HeytingLean.Quantum.OML

example {α} [BoundedLattice α] [OrthomodularLattice α] (a b : α) :
  a ⊓ (Sasaki.hook a b) ≤ b :=
  Sasaki.inf_hook_le a b

