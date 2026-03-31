import HeytingLean.Embeddings.Adelic

/-!
# Embeddings.CrossLensTransport

Cross-lens transport scaffolding.

The “unified system” spec treats per-lens states as different presentations of shared invariants
and uses RT-style contracts to move between them. This module packages that idea in a minimal,
executable-friendly form.

**Migration note:** This module uses the original `LensID` (7 lenses).
For the generalized version supporting arbitrary tag types (including
`CoreLensTag` with 71 lenses), see `GenericCrossLensTransport`.
-/

namespace HeytingLean
namespace Embeddings

/-- A lens-indexed family of carriers together with a shared “Platonic” projection type. -/
structure CrossLensTransport (Carrier : LensID → Type) (Plato : Type) where
  toPlato : ∀ lens, Carrier lens → Plato
  fromPlato : ∀ lens, Plato → Carrier lens

  /-- RT-1: round-trip identity on lens-local states. -/
  rt1 : ∀ lens (x : Carrier lens), fromPlato lens (toPlato lens x) = x

  /-- RT-2: projecting decoded data back to Plato is the identity. -/
  rt2 : ∀ lens (p : Plato), toPlato lens (fromPlato lens p) = p

namespace CrossLensTransport

variable {Carrier : LensID → Type} {Plato : Type}

/-- Induced forward map between any two lenses, via the shared Platonic projection. -/
def forward (T : CrossLensTransport Carrier Plato) (src dst : LensID) :
    Carrier src → Carrier dst :=
  fun x => T.fromPlato dst (T.toPlato src x)

/-- Induced backward map between any two lenses, via the shared Platonic projection. -/
def backward (T : CrossLensTransport Carrier Plato) (src dst : LensID) :
    Carrier dst → Carrier src :=
  fun y => T.fromPlato src (T.toPlato dst y)

theorem backward_forward (T : CrossLensTransport Carrier Plato) (src dst : LensID) (x : Carrier src) :
    T.backward src dst (T.forward src dst x) = x := by
  simp [CrossLensTransport.backward, CrossLensTransport.forward, T.rt1, T.rt2]

end CrossLensTransport

end Embeddings
end HeytingLean
