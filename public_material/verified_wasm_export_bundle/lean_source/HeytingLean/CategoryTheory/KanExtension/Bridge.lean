import HeytingLean.CategoryTheory.KanExtension.Basic
import HeytingLean.Core.Nucleus

namespace HeytingLean
namespace CategoryTheory
namespace KanExtension

open _root_.CategoryTheory

universe uK uB vB

variable {K : Type uK} [CommRing K]
variable {X Y : Grpd.{vB, uB}}
variable {L : Type*} [SemilatticeInf L] [OrderBot L]

/-- Bridge: the Kan pushforward/pullback interface is available as an adjunction. -/
noncomputable def kan_bridge_adjunction (f : X ⥤ Y) :
    pushforwardLocalSystem (K := K) f ⊣ pullbackLocalSystem (K := K) f :=
  pushforwardAdjunction (K := K) f

/-- Bridge to the nucleus side: closure operators remain inflationary. -/
theorem nucleus_extensive_bridge (N : Core.Nucleus L) (x : L) :
    x ≤ N.R x :=
  N.extensive x

end KanExtension
end CategoryTheory
end HeytingLean
