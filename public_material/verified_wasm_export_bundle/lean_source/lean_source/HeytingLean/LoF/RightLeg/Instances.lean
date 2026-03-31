import HeytingLean.LoF.RightLeg
import HeytingLean.Numbers.Surreal.NucleusCore
import HeytingLean.Numbers.SurrealCore
-- Comparison CompSpec adapter can be provided when a CompleteLattice
-- instance for `Ω_ℓ` is available in the target carrier.

/-!
# Default RightLeg instance (identity case) for Set PreGame

Carrier := Set PreGame
R_dir   := R_union ∅  (acts by S ↦ S ∪ ∅ = S)
interp  := id

This keeps the pipeline compiling today; swapping to the real LoF instance
is a one‑line change in ComparisonLoF.
-/

namespace HeytingLean
namespace LoF
namespace Default

open Classical
open Set
open HeytingLean.Numbers.SurrealCore
open HeytingLean.Numbers.Surreal

def mk : HeytingLean.LoF.RightLeg (Set (HeytingLean.Numbers.SurrealCore.PreGame)) :=
{ R_dir := HeytingLean.Numbers.Surreal.R_union (C := (∅ : Set _))
  , interp := id
  , interp_mono := by
      intro S T h; exact h
  , close_preserves_sSup := by
      intro U
      -- With C = ∅, R_union = id; therefore distribution is immediate.
      calc
        (HeytingLean.Numbers.Surreal.R_union (C := (∅ : Set _))) (sSup U)
            = (sSup U) := by simp [HeytingLean.Numbers.Surreal.R_union]
        _   = iSup (fun S : U => S.1) := by simp [sSup_eq_iSup']
        _   = iSup (fun S : U => (HeytingLean.Numbers.Surreal.R_union (C := (∅ : Set _))) (S.1)) := by
              simp [HeytingLean.Numbers.Surreal.R_union] }

/-! ### Note
If you wish to construct a `Comparison.CompSpec` from this `RightLeg`,
use `RightLeg.f`, `RightLeg.g`, and `RightLeg.gc`. This file avoids
emitting that adapter to keep instance requirements minimal.
-/

end Default
end LoF
end HeytingLean
