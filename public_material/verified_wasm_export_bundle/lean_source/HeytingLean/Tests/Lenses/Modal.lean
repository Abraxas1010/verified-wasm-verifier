import HeytingLean.LoF.Lens.Modal

open HeytingLean.LoF.Lens

def reflFrame (W : Type _) : Frame W := { R := fun w v => w = v }

example {W} (X Y : Set W) :
  Modal.I (F := reflFrame W) (X ∩ Y) =
  Modal.I (F := reflFrame W) X ∩ Modal.I (F := reflFrame W) Y :=
  Modal.inf_preserving (F := reflFrame W) (X := X) (Y := Y)

example {W} (X : Set W) :
  Modal.I (F := reflFrame W) (Modal.I (F := reflFrame W) X) = Modal.I (F := reflFrame W) X :=
  Modal.idempotent (F := reflFrame W) (X := X)
    (by intro w; rfl)
    (by intro u v z huv hvz; exact Eq.trans huv hvz)

example {W} (X : Set W) :
  Modal.I (F := reflFrame W) X ⊆ X :=
  Modal.subset_of_reflexive (F := reflFrame W) (X := X) (by intro w; rfl)
