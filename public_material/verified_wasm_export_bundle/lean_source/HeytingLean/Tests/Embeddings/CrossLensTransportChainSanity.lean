import HeytingLean.Embeddings.CrossLensTransportChain
import HeytingLean.IteratedVirtual.Globe
import HeytingLean.IteratedVirtual.GlobularCrossLensBridge

/-!
# Tests.Embeddings.CrossLensTransportChainSanity

Compile-only sanity checks for virtual chains of cross-lens transports.
-/

namespace HeytingLean.Tests.Embeddings

open HeytingLean
open HeytingLean.Embeddings

def trivialTransport : CrossLensTransport (Carrier := fun _ : LensID => Nat) (Plato := Nat) where
  toPlato := fun _ x => x
  fromPlato := fun _ p => p
  rt1 := by intro _ x; rfl
  rt2 := by intro _ p; rfl

def chain_omega_to_tensor : CrossLensTransport.Chain (Carrier := fun _ : LensID => Nat) LensID.omega LensID.tensor :=
  HeytingLean.Util.VirtualChain.cons
    (a := LensID.omega) (b := LensID.region) (c := LensID.tensor)
    (trivialTransport.forward LensID.omega LensID.region)
    (HeytingLean.Util.VirtualChain.cons
      (trivialTransport.forward LensID.region LensID.tensor)
      (HeytingLean.Util.VirtualChain.nil LensID.tensor))

example (x : Nat) :
    CrossLensTransport.compile (Carrier := fun _ : LensID => Nat) chain_omega_to_tensor x = x := by
  rfl

example :
    let X := HeytingLean.IteratedVirtual.Globe 3
    let x0 : X.Cell 0 :=
      HeytingLean.IteratedVirtual.Globe.boundary
        (k := 3) (n := 0) (by decide) (⟨0, by decide⟩)
    let p : HeytingLean.IteratedVirtual.GlobularCrossLensBridge.CellPacket
      ((X.toPresheaf).toGlobularSet) :=
      ⟨0, (HeytingLean.IteratedVirtual.GlobularSet.toPresheaf_toGlobularSetIso (X := X)).inv.map 0 x0⟩
    (HeytingLean.IteratedVirtual.GlobularCrossLensBridge.globularPacketTransport X).forward
      LensID.omega LensID.tensor p
      =
    (HeytingLean.IteratedVirtual.GlobularCrossLensBridge.globularPacketTransport X).forward
      LensID.region LensID.tensor
      ((HeytingLean.IteratedVirtual.GlobularCrossLensBridge.globularPacketTransport X).forward
        LensID.omega LensID.region p) := by
  intro X x0 p
  simpa using
    HeytingLean.IteratedVirtual.GlobularCrossLensBridge.globularPacketTransport_forward_comp
      (X := X) LensID.omega LensID.region LensID.tensor p

end HeytingLean.Tests.Embeddings
