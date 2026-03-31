import HeytingLean.LoF.Lens.SheafLT

open HeytingLean.LoF.Lens.SheafLT

-- Compile-only sanity: lemmas are available generically
example {α} [CompleteLattice α] (M : Modality α) (a b : α) :
  M.J (a ⊓ b) = M.J a ⊓ M.J b := M.map_inf a b

example {α} [CompleteLattice α] (M : Modality α) (a : α) :
  M.J (M.J a) = M.J a := M.idempotent a

