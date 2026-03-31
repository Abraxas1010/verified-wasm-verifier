import HeytingLean.Quantum.Translate.Instances.UpSet

open HeytingLean.Quantum.Translate

open HeytingLean.Quantum.OML O6

section

def F := UpSet.O6UpQLMap

example : (F).toOmega (u ⊓ v) =
  Omega.inf (M := (F).M) ((F).toOmega u) ((F).toOmega v) := by
  simpa using (F).map_inf_toOmega u v

example : Omega.inf (M := (F).M) ((F).toOmega u)
                        (Omega.imp (M := (F).M) ((F).toOmega u) ((F).toOmega v))
          ≤ (F).toOmega v :=
  (F).mp u v

end
