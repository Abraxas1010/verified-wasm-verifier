import HeytingLean.LoF.Core
import HeytingLean.LoF.Lens.Tensor
import HeytingLean.LoF.Lens.Graph
import HeytingLean.LoF.Lens.Clifford

/-!
Round-trip lens contracts scaffolding. This file sets up the module and
APIs; formal proofs will be incrementally added.
-/

namespace HeytingLean
namespace LoF
namespace Lens

open HeytingLean.LoF

structure LensOutputs (n : Nat) where
  tensor   : String
  graph    : String
  clifford : String
  deriving Repr

def computeAll {n} (canon : Canonical n) : LensOutputs n :=
  -- Re-encode all lenses from the canonical representation using
  -- the shared prefix+payload scheme.
  { tensor   := "tensor::"   ++ canon.asString
  , graph    := "graph::"    ++ canon.asString
  , clifford := "clifford::" ++ canon.asString
  }

def decodeAllToCanonical {n} (outs : LensOutputs n) (canon : Canonical n) : Canonical n :=
  -- Decode each lens-specific string back to a canonical wrapper and
  -- require that they agree; otherwise fall back to the supplied
  -- canonical representative.
  let cT := decodeTensorToCanonical outs.tensor canon
  let cG := decodeGraphToCanonical outs.graph canon
  let cC := decodeCliffordToCanonical outs.clifford canon
  if cT.asString = cG.asString ∧ cT.asString = cC.asString then
    cT
  else
    canon

end Lens
end LoF
end HeytingLean
