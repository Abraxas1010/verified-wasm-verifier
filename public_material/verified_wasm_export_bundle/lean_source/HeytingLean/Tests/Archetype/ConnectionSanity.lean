import HeytingLean.DiffGeometry.Connection.README

open _root_.CategoryTheory

example {K : Type} [CommRing K] {X : Grpd}
    (F : HeytingLean.DiffGeometry.Connection.LensConnectionFamily (K := K) (X := X))
    (l : HeytingLean.Embeddings.CoreLensTag) (a : X) :
    HeytingLean.DiffGeometry.Connection.parallelTransport (K := K) (X := X) (F l) (𝟙 a) =
      𝟙 ((F l).obj a) := by
  exact HeytingLean.DiffGeometry.Connection.identity_transport_for_each_lens (K := K) (X := X) F l a
