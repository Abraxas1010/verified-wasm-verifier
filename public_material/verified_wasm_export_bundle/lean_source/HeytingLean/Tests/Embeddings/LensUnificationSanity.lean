import HeytingLean.Embeddings.LensUnification
import HeytingLean.Embeddings.CrossLensTransport

/-!
# Tests.Embeddings.LensUnificationSanity

Compile-only sanity checks for LensID ↔ CoreLensTag bridging and generic transport.
-/

namespace HeytingLean.Tests.Embeddings.LensUnificationSanity

open HeytingLean
open HeytingLean.Embeddings

/-! ## Bridge smoke checks -/
#check LensIDCoreBridge.toCoreLensTag
#check LensIDCoreBridge.fromCoreLensTag?
#check LensIDCoreBridge.toCoreLensTag_injective
#check LensIDCoreBridge.fromCoreLensTag?_toCoreLensTag
#check LensIDCoreBridge.lensSetToLensIDs
#check LensIDCoreBridge.lensIDsToLensSet

/-! ## Round-trip verification -/
example : LensIDCoreBridge.toCoreLensTag .omega = CoreLensTag.omega := rfl
example : LensIDCoreBridge.toCoreLensTag .tensor = CoreLensTag.tensor := rfl
example : LensIDCoreBridge.toCoreLensTag .matula = CoreLensTag.matula := rfl
example : LensIDCoreBridge.fromCoreLensTag? CoreLensTag.omega = some LensID.omega := rfl
example : LensIDCoreBridge.fromCoreLensTag? CoreLensTag.tropical = none := rfl

/-! ## Generic transport smoke checks -/
#check GenericCrossLensTransport.GenericTransport
#check GenericCrossLensTransport.GenericTransport.forward
#check GenericCrossLensTransport.GenericTransport.backward
#check GenericCrossLensTransport.GenericTransport.backward_forward
#check GenericCrossLensTransport.GenericTransport.forward_comp
#check GenericCrossLensTransport.restrictToLensID
#check GenericCrossLensTransport.CrossLensTransportAlias

/-! ## Generic lens data smoke checks -/
#check GenericLensData.GenericLensData
#check GenericLensData.GenericPrecision
#check GenericLensData.GenericApprox
#check GenericLensData.toLensData
#check GenericLensData.ofLensData

/-! ## Generic chain smoke checks -/
#check GenericCrossLensTransport.Step
#check GenericCrossLensTransport.Chain
#check GenericCrossLensTransport.compile

/-! ## LensTag instance on LensID -/
example : LensTag.name (τ := LensID) LensID.omega = "Omega (Eigenform)" := rfl
example : LensTag.id (τ := LensID) LensID.tensor = "core.tensor" := rfl

/-! ## Concrete generic transport (trivial Nat carrier) -/
def trivialGenericTransport :
    GenericCrossLensTransport.GenericTransport CoreLensTag
      (fun _ => Nat) Nat where
  toPlato _ x := x
  fromPlato _ p := p
  rt1 _ _ := rfl
  rt2 _ _ := rfl

example (x : Nat) :
    trivialGenericTransport.forward CoreLensTag.omega CoreLensTag.tropical x = x := rfl

example (x : Nat) :
    trivialGenericTransport.backward CoreLensTag.graph CoreLensTag.density x = x := rfl

/-! ## Restriction bridge -/
def restrictedTransport :=
  GenericCrossLensTransport.restrictToLensID trivialGenericTransport

example (x : Nat) :
    restrictedTransport.forward LensID.omega LensID.tensor x = x := rfl

/-! ## LensSet interop -/
example : (LensIDCoreBridge.lensIDsToLensSet [.omega, .tensor]).size ≥ 1 := by
  decide

/-! ## Backwards-compatibility check: old CrossLensTransport still works -/
#check @CrossLensTransport
#check @CrossLensTransport.forward
#check @CrossLensTransport.backward_forward

end HeytingLean.Tests.Embeddings.LensUnificationSanity
