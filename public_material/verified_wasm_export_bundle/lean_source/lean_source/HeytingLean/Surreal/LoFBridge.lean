import HeytingLean.Numbers.Surreal.LoFDerivation

/-!
# Surreal.LoFBridge

Compatibility module exposing surreal/LoF bridge theorems under a stable path.
-/

namespace HeytingLean.Surreal.LoFBridge

open HeytingLean.Numbers.Surreal

/-- Surreal constructor as LoF distinction (raw shape theorem). -/
theorem constructor_as_lof_distinction
    (L R : List HeytingLean.Numbers.SurrealCore.PreGame) :
    LoFDerivation.GameDistinction.toPreGameRaw ({ inside := L, outside := R } : LoFDerivation.GameDistinction)
      = ({ L := L, R := R, birth := 0 } : HeytingLean.Numbers.SurrealCore.PreGame) :=
  LoFDerivation.lof_distinction_is_surreal_constructor L R

/-- LoF void distinction corresponds to surreal zero. -/
theorem void_corresponds_to_zero :
    LoFDerivation.GameDistinction.toPreGameRaw
        ({ inside := ([] : List HeytingLean.Numbers.SurrealCore.PreGame),
           outside := ([] : List HeytingLean.Numbers.SurrealCore.PreGame) } :
          LoFDerivation.GameDistinction)
      = (HeytingLean.Numbers.Surreal.LoFDerivation.SurrealCore.PreGame.zero :
          HeytingLean.Numbers.SurrealCore.PreGame) :=
  LoFDerivation.void_is_zero

end HeytingLean.Surreal.LoFBridge
