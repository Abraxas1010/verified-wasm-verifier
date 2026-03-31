import HeytingLean.Quantum.Translate.Instances.UpSetNucleus

open HeytingLean.Quantum.Translate
open HeytingLean.Quantum.OML O6

section

def C : Set O6 := {x | x = u}
def FN := O6UpQLMapN (C := C)

example : (FN).toOmega (u ⊓ v) =
  Omega.inf (M := (FN).M) ((FN).toOmega u) ((FN).toOmega v) := by
  simpa using (FN).map_inf_toOmega u v

-- Modus ponens holds on Ω_J even with non‑identity nucleus
example : Omega.inf (M := (FN).M) ((FN).toOmega u)
                        (Omega.imp (M := (FN).M) ((FN).toOmega u) ((FN).toOmega v))
          ≤ (FN).toOmega v :=
  (FN).mp u v

end

