import HeytingLean.Topos.LocSys

import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Fin

/-!
LocSys smoke test (compile-only).

This checks that the basic “local systems over groupoids + external tensor” scaffold compiles.
-/

namespace HeytingLean
namespace Tests
namespace Topos

open CategoryTheory

section
  abbrev K := ℚ
  abbrev G := Multiplicative (ZMod 2)
  abbrev H := Multiplicative (ZMod 3)
  abbrev S2 := Equiv.Perm (Fin 2)

  #check HeytingLean.Topos.LocSys.Coeff K
  #check HeytingLean.Topos.LocSys.Base1.BG (G := G)
  #check HeytingLean.Topos.LocSys.Base1.BG (G := H)

  #check HeytingLean.Topos.LocSys.Examples.BGReps.trivial (K := K) (G := G)
  #check HeytingLean.Topos.LocSys.Examples.BGReps.trivial (K := K) (G := H)
  #check HeytingLean.Topos.LocSys.Examples.BGReps.signPermFin2 (K := K)
  #check HeytingLean.Topos.LocSys.Loc.externalTensor (K := K)

  -- Pullback along a `BG` map induced by a group homomorphism (here: identity).
  noncomputable def pullbackTrivial :
      HeytingLean.Topos.LocSys.LocalSystem (K := K) (HeytingLean.Topos.LocSys.Base1.BG (G := G)) :=
    (HeytingLean.Topos.LocSys.LocalSystems.pullback (K := K) (MonoidHom.id G).toFunctor).obj
      (HeytingLean.Topos.LocSys.Examples.BGReps.trivial (K := K) (G := G))

  -- Pushforward along the identity (left Kan extension).
  noncomputable def pushforwardTrivial :
      HeytingLean.Topos.LocSys.LocalSystem (K := K) (HeytingLean.Topos.LocSys.Base1.BG (G := G)) :=
    (HeytingLean.Topos.LocSys.LocalSystems.pushforward (K := K) (MonoidHom.id G).toFunctor).obj
      (HeytingLean.Topos.LocSys.Examples.BGReps.trivial (K := K) (G := G))

  #check HeytingLean.Topos.LocSys.LocalSystems.pushforwardAdjunction (K := K) (X := HeytingLean.Topos.LocSys.Base1.BG (G := G))

  -- External tensor over `BG×BH`.
  noncomputable def extTensorTrivial :
      HeytingLean.Topos.LocSys.LocalSystem (K := K)
        (HeytingLean.Topos.LocSys.Base1.prod
          (HeytingLean.Topos.LocSys.Base1.BG (G := G))
          (HeytingLean.Topos.LocSys.Base1.BG (G := H))) :=
    HeytingLean.Topos.LocSys.LocalSystems.externalTensor (K := K)
      (HeytingLean.Topos.LocSys.Examples.BGReps.trivial (K := K) (G := G))
      (HeytingLean.Topos.LocSys.Examples.BGReps.trivial (K := K) (G := H))

  -- A nontrivial `BG`-local system (sign rep of `S₂`), pulled back along the identity.
  noncomputable def pullbackSign :
      HeytingLean.Topos.LocSys.LocalSystem (K := K) (HeytingLean.Topos.LocSys.Base1.BG (G := S2)) :=
    (HeytingLean.Topos.LocSys.LocalSystems.pullback (K := K) (MonoidHom.id S2).toFunctor).obj
      (HeytingLean.Topos.LocSys.Examples.BGReps.signPermFin2 (K := K))

  -- External tensor of the nontrivial `S₂` sign local system with itself over `BG×BG`.
  noncomputable def extTensorSign :
      HeytingLean.Topos.LocSys.LocalSystem (K := K)
        (HeytingLean.Topos.LocSys.Base1.prod
          (HeytingLean.Topos.LocSys.Base1.BG (G := S2))
          (HeytingLean.Topos.LocSys.Base1.BG (G := S2))) :=
    HeytingLean.Topos.LocSys.LocalSystems.externalTensor (K := K)
      (HeytingLean.Topos.LocSys.Examples.BGReps.signPermFin2 (K := K))
      (HeytingLean.Topos.LocSys.Examples.BGReps.signPermFin2 (K := K))
end

end Topos
end Tests
end HeytingLean
