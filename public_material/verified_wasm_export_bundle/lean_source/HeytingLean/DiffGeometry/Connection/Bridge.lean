import HeytingLean.DiffGeometry.Connection.Basic
import HeytingLean.Embeddings.CoreLenses

namespace HeytingLean
namespace DiffGeometry
namespace Connection

open _root_.CategoryTheory

universe uK uB vB

variable {K : Type uK} [CommRing K]
variable {X : Grpd.{vB, uB}}

/-- Lens-indexed family of flat connections on the same base. -/
abbrev LensConnectionFamily :=
  Embeddings.CoreLensTag → FlatConnection (K := K) (X := X)

theorem identity_transport_for_each_lens (F : LensConnectionFamily (K := K) (X := X))
    (l : Embeddings.CoreLensTag) (a : X) :
    parallelTransport (K := K) (X := X) (F l) (𝟙 a) = 𝟙 ((F l).obj a) := by
  simpa using parallelTransport_id (K := K) (X := X) (F l) a

end Connection
end DiffGeometry
end HeytingLean
