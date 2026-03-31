/-
  Certified lens infrastructure.

  A lens carries computational transformations (`forward`/`backward`) and
  proof-only round-trip certificates (RT-1 / RT-2).
-/

import HeytingLean.Certified.Basic
import HeytingLean.Lens.PCB.Distance

namespace HeytingLean
namespace Lens

open HeytingLean.Certified

universe u

/-- Lens identifier (broad “architecture” tags). -/
inductive LensId
  | Tensor
  | Graph
  | Topology
  | Clifford
  | Sheaf
  | CausalDAG
  | PetriNet
  | Homotopy
deriving DecidableEq, Repr

/-- Round-trip contract levels. -/
inductive RTLevel
  | RT1  -- Lossless round-trip
  | RT2  -- Lossy but bounded
deriving DecidableEq, Repr

/-- Lens with certified round-trip.

RT-2 bounds are stated relative to a supplied `PCB.Distance` instance on the source type. -/
structure CertifiedLens (α β : Type u) where
  forward : α → β
  backward : β → α
  rtLevel : RTLevel
  /-- RT-1: perfect round-trip. -/
  rt1_proof : rtLevel = RTLevel.RT1 → ∀ a, backward (forward a) = a
  /-- RT-2: bounded approximation (w.r.t. a supplied distance). -/
  rt2_bound :
    rtLevel = RTLevel.RT2 →
      [HeytingLean.Lens.PCB.Distance α] →
        ∃ ε : Real, ∀ a,
          HeytingLean.Lens.PCB.Distance.dist (backward (forward a)) a < ε

namespace CertifiedLens

/-- Apply lens forward (computational, compiles to runtime code). -/
@[inline] def apply {α β : Type u} (lens : CertifiedLens α β) (a : α) : β :=
  lens.forward a

end CertifiedLens

/-- Certified transformation through a lens (pairs output with proof-only obligations). -/
structure LensTransform (α β : Type u) (Spec : β → Prop) where
  lens : CertifiedLens α β
  input : α
  output : Certified β Spec
  /-- Output is lens application of input. -/
  isTransform : output.val = lens.forward input

namespace LensTransform

/-- Extract just the output (proofs erased). -/
@[inline] def extract {α β : Type u} {Spec : β → Prop} (t : LensTransform α β Spec) : β :=
  t.output.val

end LensTransform

end Lens
end HeytingLean

