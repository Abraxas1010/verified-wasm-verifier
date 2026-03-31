import HeytingLean.DiffGeometry.Connection.Bridge

namespace HeytingLean
namespace Bridges
namespace Archetype

open _root_.CategoryTheory

theorem connection_to_lens_transport_bound
    {K : Type} [CommRing K] {X : Grpd}
    (F : DiffGeometry.Connection.LensConnectionFamily (K := K) (X := X))
    (l : Embeddings.CoreLensTag) (a : X) :
    DiffGeometry.Connection.parallelTransport (K := K) (X := X) (F l) (𝟙 a) =
      𝟙 ((F l).obj a) := by
  exact DiffGeometry.Connection.identity_transport_for_each_lens (K := K) (X := X) F l a

end Archetype
end Bridges
end HeytingLean
