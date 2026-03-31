import HeytingLean.LoF.Lens.Truncation

open HeytingLean.LoF.Lens.Truncation

-- Compile-only sanity for `n`‑truncation interface
example {α} [CompleteLattice α] (L : Level α) (a b : α) :
  L.J (a ⊓ b) = L.J a ⊓ L.J b := L.map_inf a b

example {α} [CompleteLattice α] (L : Level α) (a : α) :
  L.J (L.J a) = L.J a := L.idempotent a

