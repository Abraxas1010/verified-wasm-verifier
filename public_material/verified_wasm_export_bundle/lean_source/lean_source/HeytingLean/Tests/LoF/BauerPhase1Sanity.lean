import HeytingLean.LoF.Bauer
import HeytingLean.LoF.ComparisonNucleus.Examples

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF

namespace ComparisonPhase1

open HeytingLean.LoF.Comparison

noncomputable def boolStrongHyp : StrongHyp Bool Bool :=
{ boolCompSpec with
  map_inf := by
    intro x y
    rfl }

noncomputable def boolGeom :
    HeytingLean.LoF.Bauer.FrameGeomEmbedding (A := ΩR (boolStrongHyp : CompSpec Bool Bool)) (B := Bool) :=
  Comparison.comparisonGeomEmbedding (S := boolStrongHyp) (htop := rfl)

example (a : ΩR (boolStrongHyp : CompSpec Bool Bool)) :
    boolGeom.decode (boolGeom.encode a) = a := by
  simpa [boolGeom] using (boolGeom.round a)

example (a b : ΩR (boolStrongHyp : CompSpec Bool Bool)) :
    boolGeom.encode (a ⊓ b) = boolGeom.encode a ⊓ boolGeom.encode b := by
  simp [boolGeom]

example (s : Set (ΩR (boolStrongHyp : CompSpec Bool Bool))) :
    boolGeom.encode (sSup s) = sSup (boolGeom.encode '' s) := by
  simp [boolGeom]

end ComparisonPhase1

end LoF
end Tests
end HeytingLean
