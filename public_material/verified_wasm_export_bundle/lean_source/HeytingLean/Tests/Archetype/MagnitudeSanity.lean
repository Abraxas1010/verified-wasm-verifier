import HeytingLean.Metrics.Magnitude.README
import HeytingLean.Bridges.Archetype.MagnitudeToAdelic

example :
    HeytingLean.Metrics.Magnitude.finiteMagnitude (Fin 3) = 3 := by
  native_decide

example :
    HeytingLean.Metrics.Magnitude.finiteMagnitude (PUnit ⊕ PUnit) = 2 := by
  native_decide

example :
    HeytingLean.Metrics.Magnitude.finiteMagnitude HeytingLean.Embeddings.LensID = 7 := by
  exact HeytingLean.Metrics.Magnitude.finiteMagnitude_lensID

example :
    HeytingLean.Metrics.Magnitude.finiteMagnitude
      (Fin HeytingLean.Embeddings.CoreLensTag.count) =
      HeytingLean.Embeddings.CoreLensTag.count := by
  exact HeytingLean.Metrics.Magnitude.finiteMagnitude_coreLensIndex

example :
    HeytingLean.Metrics.Magnitude.finiteMagnitude HeytingLean.Embeddings.LensID ≤
      HeytingLean.Embeddings.CoreLensTag.count := by
  exact HeytingLean.Bridges.Archetype.magnitude_to_adelic_core_capacity
