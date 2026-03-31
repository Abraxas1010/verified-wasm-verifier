import HeytingLean.Embeddings.CrossLensTransportChain
import HeytingLean.IteratedVirtual.GlobularRoundTrip

/-!
# IteratedVirtual.GlobularCrossLensBridge

Bridge globular structured↔presheaf round-trip isomorphisms into the
cross-lens transport interface by transporting whole cell packets.

Note:
- This certifies non-trivial transport coherence (round-trip via the actual iso).
- It does not identify `LensID` with globular dimensions; that requires a separate
  index-level embedding layer.
-/

namespace HeytingLean
namespace IteratedVirtual
namespace GlobularCrossLensBridge

open HeytingLean.Embeddings

abbrev CellPacket (X : GlobularSet) : Type _ :=
  Sigma X.Cell

def toRoundTripPacket (X : GlobularSet) :
    CellPacket X → CellPacket ((X.toPresheaf).toGlobularSet)
  | ⟨n, x⟩ =>
      ⟨n, (GlobularSet.toPresheaf_toGlobularSetIso (X := X)).inv.map n x⟩

def fromRoundTripPacket (X : GlobularSet) :
    CellPacket ((X.toPresheaf).toGlobularSet) → CellPacket X
  | ⟨n, x⟩ =>
      ⟨n, (GlobularSet.toPresheaf_toGlobularSetIso (X := X)).hom.map n x⟩

@[simp] theorem from_toRoundTripPacket (X : GlobularSet) (p : CellPacket X) :
    fromRoundTripPacket X (toRoundTripPacket X p) = p := by
  rcases p with ⟨n, x⟩
  rfl

@[simp] theorem to_fromRoundTripPacket (X : GlobularSet)
    (p : CellPacket ((X.toPresheaf).toGlobularSet)) :
    toRoundTripPacket X (fromRoundTripPacket X p) = p := by
  rcases p with ⟨n, x⟩
  rfl

/-- Cross-lens transport induced by the structured↔presheaf round-trip isomorphism. -/
def globularPacketTransport (X : GlobularSet) :
    CrossLensTransport
      (Carrier := fun _ : LensID => CellPacket ((X.toPresheaf).toGlobularSet))
      (Plato := CellPacket X) where
  toPlato := fun _ => fromRoundTripPacket X
  fromPlato := fun _ => toRoundTripPacket X
  rt1 := by
    intro _ p
    exact to_fromRoundTripPacket (X := X) p
  rt2 := by
    intro _ p
    exact from_toRoundTripPacket (X := X) p

theorem globularPacketTransport_forward_comp (X : GlobularSet)
    (src mid dst : LensID)
    (p : CellPacket ((X.toPresheaf).toGlobularSet)) :
    (globularPacketTransport X).forward src dst p =
      (globularPacketTransport X).forward mid dst
        ((globularPacketTransport X).forward src mid p) := by
  exact
    CrossLensTransport.forward_comp
      (T := globularPacketTransport X) src mid dst p

end GlobularCrossLensBridge
end IteratedVirtual
end HeytingLean
