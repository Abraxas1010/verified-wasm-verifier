import HeytingLean.CategoryTheory.KanExtension.Bridge

namespace HeytingLean
namespace Bridges
namespace Archetype

open _root_.CategoryTheory

universe uK uB vB

variable {K : Type uK} [CommRing K]
variable {X Y : Grpd.{vB, uB}}
variable {L : Type*} [SemilatticeInf L] [OrderBot L]

theorem kan_to_nucleus_interface (f : X ⥤ Y) (N : Core.Nucleus L) (x : L) :
    (x ≤ N.R x) ∧
      Nonempty
        (CategoryTheory.KanExtension.pushforwardLocalSystem (K := K) f ⊣
          CategoryTheory.KanExtension.pullbackLocalSystem (K := K) f) := by
  refine ⟨CategoryTheory.KanExtension.nucleus_extensive_bridge N x, ?_⟩
  exact ⟨CategoryTheory.KanExtension.kan_bridge_adjunction (K := K) f⟩

end Archetype
end Bridges
end HeytingLean
