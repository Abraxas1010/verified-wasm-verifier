import HeytingLean.LoF.Lens.Trace

open HeytingLean.LoF.Lens

example {α} (X Y : Set (List α)) :
  I (α := α) (X ∩ Y) = I (α := α) X ∩ I (α := α) Y := I.inf_preserving (X := X) (Y := Y)

example {α} (X : Set (List α)) : I (α := α) (I (α := α) X) = I (α := α) X :=
  I.idempotent (X := X)

