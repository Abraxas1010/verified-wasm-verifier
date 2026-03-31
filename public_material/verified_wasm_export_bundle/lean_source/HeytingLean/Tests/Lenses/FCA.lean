import HeytingLean.LoF.Lens.FCA

open HeytingLean.LoF.Lens.FCA

-- Simple dummy context: every object holds every attribute
def trivialCtx (O A : Type _) : Context O A := { holds := fun _ _ => True }

example {O A} (X Y : Set A) :
  J (C := trivialCtx O A) (X ∩ Y) ⊆
  J (C := trivialCtx O A) X ∩ J (C := trivialCtx O A) Y :=
  J.inf_preserving_left (C := trivialCtx O A) (X := X) (Y := Y)

example {O A} (X : Set A) :
  J (C := trivialCtx O A) (J (C := trivialCtx O A) X) =
  J (C := trivialCtx O A) X :=
  J.idempotent (C := trivialCtx O A) (X := X)
