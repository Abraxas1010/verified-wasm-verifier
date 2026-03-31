import HeytingLean.Embeddings.LensRegistry
import HeytingLean.Embeddings.LensIDCoreBridge
import HeytingLean.Embeddings.PerspectivalDescentCarrier

namespace HeytingLean
namespace Embeddings
namespace GenericCrossLensTransport

universe u v

/-- A tag-indexed family of carriers with a shared Platonic projection type.
Generalizes `CrossLensTransport` to any tag type `τ`. -/
structure GenericTransport (τ : Type u) (Carrier : τ → Type v) (Plato : Type v) where
  toPlato : ∀ tag, Carrier tag → Plato
  fromPlato : ∀ tag, Plato → Carrier tag
  /-- RT-1: round-trip identity on tag-local states. -/
  rt1 : ∀ tag (x : Carrier tag), fromPlato tag (toPlato tag x) = x
  /-- RT-2: projecting decoded data back to Plato is the identity. -/
  rt2 : ∀ tag (p : Plato), toPlato tag (fromPlato tag p) = p

namespace GenericTransport

variable {τ : Type u} {Carrier : τ → Type v} {Plato : Type v}

/-- Forward map between any two tags via the shared Platonic projection. -/
def forward (T : GenericTransport τ Carrier Plato) (src dst : τ) :
    Carrier src → Carrier dst :=
  fun x => T.fromPlato dst (T.toPlato src x)

/-- Backward map between any two tags via the shared Platonic projection. -/
def backward (T : GenericTransport τ Carrier Plato) (src dst : τ) :
    Carrier dst → Carrier src :=
  fun y => T.fromPlato src (T.toPlato dst y)

/-- Backward ∘ forward = id. -/
theorem backward_forward (T : GenericTransport τ Carrier Plato) (src dst : τ)
    (x : Carrier src) :
    T.backward src dst (T.forward src dst x) = x := by
  simp [backward, forward, T.rt1, T.rt2]

/-- Forward composition through the Platonic factorization. -/
theorem forward_comp (T : GenericTransport τ Carrier Plato) (src mid dst : τ)
    (x : Carrier src) :
    T.forward src dst x = T.forward mid dst (T.forward src mid x) := by
  simp [forward, T.rt2]

/-- Cocycle law for forward transport maps. -/
def ForwardCocycle (T : GenericTransport τ Carrier Plato) : Prop :=
  ∀ a b c (x : Carrier a), T.forward a c x = T.forward b c (T.forward a b x)

/-- `forward_comp` is exactly the transport cocycle condition. -/
theorem forward_comp_is_cocycle (T : GenericTransport τ Carrier Plato) :
    ForwardCocycle T := by
  intro a b c x
  simpa [ForwardCocycle] using T.forward_comp a b c x

/--
Every exact round-trip transport induces a PDC structure:
integral elements are fixed points of the local round-trip map.
-/
def toPDC (T : GenericTransport τ Carrier Plato) :
    PerspectivalDescentCarrier τ Carrier where
  integral t := {x | T.fromPlato t (T.toPlato t x) = x}
  finiteness x := by
    have hEmpty : {t : τ | x t ∉ ({y : Carrier t | T.fromPlato t (T.toPlato t y) = y} : Set (Carrier t))} = ∅ := by
      ext t
      simp [T.rt1]
    rw [hEmpty]
    exact (Set.finite_empty : (∅ : Set τ).Finite)
  truncate t _ x := T.fromPlato t (T.toPlato t x)

end GenericTransport

/-- Legacy alias: the original transport shape as a specialization to `LensID`. -/
abbrev CrossLensTransportAlias (Carrier : LensID → Type) (Plato : Type) :=
  GenericTransport LensID Carrier Plato

/-- Restrict a `CoreLensTag`-indexed transport to the 7-lens `LensID` subset. -/
def restrictToLensID
    {Carrier : CoreLensTag → Type v} {Plato : Type v}
    (T : GenericTransport CoreLensTag Carrier Plato) :
    GenericTransport LensID (fun l => Carrier (LensIDCoreBridge.toCoreLensTag l)) Plato where
  toPlato l := T.toPlato (LensIDCoreBridge.toCoreLensTag l)
  fromPlato l := T.fromPlato (LensIDCoreBridge.toCoreLensTag l)
  rt1 l := T.rt1 (LensIDCoreBridge.toCoreLensTag l)
  rt2 l := T.rt2 (LensIDCoreBridge.toCoreLensTag l)

end GenericCrossLensTransport
end Embeddings
end HeytingLean
