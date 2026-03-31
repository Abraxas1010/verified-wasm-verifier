import HeytingLean.Util.VirtualChain
import HeytingLean.Embeddings.CrossLensTransport

/-!
# Embeddings.CrossLensTransportChain

Systematic reuse of the “virtualization via chains” pattern for cross-lens transport:

- One step from lens `ℓ₁` to `ℓ₂` is a function `Carrier ℓ₁ → Carrier ℓ₂`.
- A multi-step transport is a `VirtualChain` of such functions over intermediate lens IDs.
- You can compile the chain into an actual function by composing the steps.

When the steps come from a `CrossLensTransport`, they collapse to the direct `forward` map.
-/

namespace HeytingLean
namespace Embeddings

open HeytingLean.Util

namespace CrossLensTransport

variable {Carrier : LensID → Type} {Plato : Type}

abbrev Step (Carrier : LensID → Type) (src dst : LensID) : Type :=
  Carrier src → Carrier dst

abbrev Chain (Carrier : LensID → Type) (src dst : LensID) : Type 1 :=
  VirtualChain (Step Carrier) src dst

def compile {src dst : LensID} : Chain Carrier src dst → (Carrier src → Carrier dst)
  | .nil _ => fun x => x
  | .cons f rest => (compile rest) ∘ f

theorem forward_comp (T : CrossLensTransport Carrier Plato) (src mid dst : LensID) (x : Carrier src) :
    T.forward src dst x = T.forward mid dst (T.forward src mid x) := by
  simp [CrossLensTransport.forward, T.rt2]

end CrossLensTransport

end Embeddings
end HeytingLean
