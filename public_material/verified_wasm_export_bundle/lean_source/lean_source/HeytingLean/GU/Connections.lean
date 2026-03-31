import HeytingLean.GU.Bundles
import HeytingLean.GU.Observerse

/-!
# GU.Connections (abstract interface)

Connections/covariant derivatives are central to GU (gravity + gauge).
We keep this layer abstract as an interface so downstream code can state equations
without committing to a particular differential-geometry backend yet.
-/

namespace HeytingLean
namespace GU

universe u v w

structure Connection {X : Type u} (E : Bundle (X := X)) where
  /-- A covariant derivative operator on sections, left abstract. -/
  D : Section E → Section E

/-! ### Fiberwise “connection-like” endomorphisms

For many GU statements we want something that *pulls back* cleanly along an observer embedding.
The following `PointConnection` is a minimal, fiberwise endomorphism field; it induces an
endomorphism on sections by evaluation.
-/

structure PointConnection {X : Type u} (E : Bundle (X := X)) where
  A : ∀ x : X, E.fiber x → E.fiber x

namespace PointConnection

variable {X : Type u} {E : Bundle (X := X)}

def toConnection (pc : PointConnection (E := E)) : Connection E :=
  { D := fun s x => pc.A x (s x) }

variable {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Pull back a fiberwise endomorphism field along an observer embedding. -/
def pullback (obs : Observerse X Y) (E : Bundle (X := Y)) (pc : PointConnection (E := E)) :
    PointConnection (E := Bundle.pullback obs E) :=
  { A := fun x => pc.A (obs.toFun x) }

end PointConnection

end GU
end HeytingLean
