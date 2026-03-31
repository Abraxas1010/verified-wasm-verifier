import HeytingLean.Metrics.Magnitude.Bridge

namespace HeytingLean
namespace Bridges
namespace Archetype

def lensIDToCoreIndex : Embeddings.LensID ↪ Fin Embeddings.CoreLensTag.count where
  toFun
    | .omega => ⟨0, by decide⟩
    | .region => ⟨1, by decide⟩
    | .graph => ⟨2, by decide⟩
    | .clifford => ⟨3, by decide⟩
    | .tensor => ⟨4, by decide⟩
    | .topology => ⟨5, by decide⟩
    | .matula => ⟨6, by decide⟩
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp at h <;> rfl

theorem magnitude_to_adelic_index_card :
    Metrics.Magnitude.finiteMagnitude Embeddings.LensID = 7 := by
  exact Metrics.Magnitude.finiteMagnitude_lensID

theorem magnitude_to_adelic_core_capacity :
    Metrics.Magnitude.finiteMagnitude Embeddings.LensID ≤ Embeddings.CoreLensTag.count := by
  calc
    Metrics.Magnitude.finiteMagnitude Embeddings.LensID ≤
        Metrics.Magnitude.finiteMagnitude (Fin Embeddings.CoreLensTag.count) :=
      Metrics.Magnitude.finiteMagnitude_le_of_embedding lensIDToCoreIndex
    _ = Embeddings.CoreLensTag.count := Metrics.Magnitude.finiteMagnitude_coreLensIndex

end Archetype
end Bridges
end HeytingLean
