import HeytingLean.Topos.LocSys.LocalSystems

namespace HeytingLean
namespace DiffGeometry
namespace Connection

open _root_.CategoryTheory

universe uK uB vB

variable {K : Type uK} [CommRing K]
variable {X : Grpd.{vB, uB}}

/-- A flat connection modelled as a local system on a base groupoid. -/
abbrev FlatConnection :=
  Topos.LocSys.LocalSystem (K := K) X

def parallelTransport (V : FlatConnection (K := K) (X := X)) {a b : X} (g : a ⟶ b) :
    V.obj a ⟶ V.obj b :=
  V.map g

def holonomy (V : FlatConnection (K := K) (X := X)) {a : X} (g : a ⟶ a) :
    V.obj a ⟶ V.obj a :=
  parallelTransport (K := K) (X := X) V g

theorem parallelTransport_id (V : FlatConnection (K := K) (X := X)) (a : X) :
    parallelTransport (K := K) (X := X) V (𝟙 a) = 𝟙 (V.obj a) := by
  simp [parallelTransport]

theorem parallelTransport_comp (V : FlatConnection (K := K) (X := X))
    {a b c : X} (f : a ⟶ b) (g : b ⟶ c) :
    parallelTransport (K := K) (X := X) V (f ≫ g) =
      parallelTransport (K := K) (X := X) V f ≫
      parallelTransport (K := K) (X := X) V g := by
  simp [parallelTransport]

theorem holonomy_id (V : FlatConnection (K := K) (X := X)) (a : X) :
    holonomy (K := K) (X := X) V (𝟙 a) = 𝟙 (V.obj a) := by
  simpa [holonomy] using parallelTransport_id (K := K) (X := X) V a

end Connection
end DiffGeometry
end HeytingLean
