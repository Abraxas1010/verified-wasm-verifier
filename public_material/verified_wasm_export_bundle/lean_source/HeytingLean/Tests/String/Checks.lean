import HeytingLean.Physics.String.Checks

/-!
Compile-only sanity checks for the small String modules (Q-series + modular).
-/ 

namespace HeytingLean
namespace Tests
namespace String

open HeytingLean.Physics.String

-- Tiny VOAGraded example
def Gdemo : VOAGraded Unit := { weights := #[0,1,1,2] }

noncomputable def _checkCharNonneg : Bool :=
  HeytingLean.Physics.String.charTruncNonneg Gdemo

-- Minimal modular matrices (identity), idempotence should hold trivially
def MId : ModMatrices :=
  let id2 : Array (Array Float) := #[(#[(1.0),(0.0)]), (#[(0.0),(1.0)])]
  { S := id2, T := id2 }

def NId : QNucleus := { mats := MId, steps := 2 }

def qdemo : QSeries := { coeffs := #[(1.0),(0.0)] }

noncomputable def _checkIdem : Bool :=
  HeytingLean.Physics.String.projectIdemCheck NId qdemo

end String
end Tests
end HeytingLean
