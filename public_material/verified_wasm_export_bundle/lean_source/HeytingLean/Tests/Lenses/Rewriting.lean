import HeytingLean.LoF.Lens.Rewriting

open HeytingLean.LoF.Lens.Rewriting

-- Trivial rewrite: only reflexive steps
def reflStep {τ} : τ → τ → Prop := fun x y => x = y

example {τ} (X Y : Set τ) :
  I (step := reflStep) (X ∩ Y) = I (step := reflStep) X ∩ I (step := reflStep) Y :=
  I.inf_preserving (step := reflStep) (X := X) (Y := Y)

example {τ} (X : Set τ) : I (step := reflStep) (I (step := reflStep) X) = I (step := reflStep) X :=
  I.idempotent (step := reflStep) (X := X)

