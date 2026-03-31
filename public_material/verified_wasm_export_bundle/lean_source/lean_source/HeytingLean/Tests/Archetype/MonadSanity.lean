import HeytingLean.CategoryTheory.Monad.README

example : HeytingLean.CDL.RNucleusMonad Id :=
  HeytingLean.CategoryTheory.Monad.id_is_r_nucleus_monad

example : HeytingLean.CDL.RNucleusMonad Option :=
  HeytingLean.CategoryTheory.Monad.option_is_r_nucleus_monad

example {L : Type} [SemilatticeInf L] [OrderBot L]
    (N : HeytingLean.Core.Nucleus L) (x : L) :
    N.R (N.R x) = N.R x := by
  exact HeytingLean.CategoryTheory.Monad.nucleus_idempotent_bridge N x
