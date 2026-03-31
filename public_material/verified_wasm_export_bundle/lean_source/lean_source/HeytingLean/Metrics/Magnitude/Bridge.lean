import HeytingLean.Metrics.Magnitude.Basic
import HeytingLean.Embeddings.Adelic
import HeytingLean.Embeddings.CoreLenses

namespace HeytingLean
namespace Metrics
namespace Magnitude

instance : Fintype Embeddings.LensID where
  elems := { Embeddings.LensID.omega, Embeddings.LensID.region, Embeddings.LensID.graph
    , Embeddings.LensID.clifford, Embeddings.LensID.tensor
    , Embeddings.LensID.topology, Embeddings.LensID.matula }
  complete := by
    intro x
    cases x <;> simp

theorem finiteMagnitude_lensID :
    finiteMagnitude Embeddings.LensID = 7 := by
  native_decide

theorem finiteMagnitude_coreLensIndex :
    finiteMagnitude (Fin Embeddings.CoreLensTag.count) = Embeddings.CoreLensTag.count := by
  simp [finiteMagnitude]

end Magnitude
end Metrics
end HeytingLean
