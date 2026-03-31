import HeytingLean.Embeddings.PerspectivalDescentCarrier

/-!
# Embeddings.PerspectivalDescentHierarchy

Layered PDC hierarchy:
- `PerspectivalDescentCarrier`: integral/finiteness/truncation
- `PDCWithTransport`: adds perspective transport through a shared Plato layer
- `PDCWithDescent`: adds matching-family + amalgamation
-/

namespace HeytingLean
namespace Embeddings

universe u v

/--
`PDCWithTransport` extends the base PDC with exact round-trip transport through
`Plato`.
-/
class PDCWithTransport (τ : Type u) (Carrier : τ → Type v)
    extends PerspectivalDescentCarrier τ Carrier where
  Plato : Type v
  toPlato : ∀ t, Carrier t → Plato
  fromPlato : ∀ t, Plato → Carrier t
  rt1 : ∀ t (x : Carrier t), fromPlato t (toPlato t x) = x
  rt2 : ∀ t (p : Plato), toPlato t (fromPlato t p) = p

namespace PDCWithTransport

variable {τ : Type u} {Carrier : τ → Type v} [P : PDCWithTransport τ Carrier]

/-- Forward transport between two perspectives via the shared `Plato` layer. -/
def forward (src dst : τ) : Carrier src → Carrier dst :=
  fun x => P.fromPlato dst (P.toPlato src x)

/-- Backward transport between two perspectives via the shared `Plato` layer. -/
def backward (src dst : τ) : Carrier dst → Carrier src :=
  fun y => P.fromPlato src (P.toPlato dst y)

/-- Backward ∘ forward is identity for exact transport. -/
theorem backward_forward (src dst : τ) (x : Carrier src) :
    backward src dst (forward src dst x) = x := by
  simp [backward, forward, P.rt1, P.rt2]

/-- Forward composition factors through the same `Plato` value. -/
theorem forward_comp (src mid dst : τ) (x : Carrier src) :
    forward src dst x = forward mid dst (forward src mid x) := by
  simp [forward, P.rt2]

/-- Cocycle formulation of forward transport. -/
def ForwardCocycle : Prop :=
  ∀ a b c (x : Carrier a), forward a c x = forward b c (forward a b x)

/-- Exact transport implies cocycle coherence. -/
theorem forward_is_cocycle :
    PDCWithTransport.ForwardCocycle (τ := τ) (Carrier := Carrier) := by
  intro a b c x
  simpa [PDCWithTransport.ForwardCocycle] using (forward_comp a b c x)

end PDCWithTransport

/--
`PDCWithDescent` adds a matching-family predicate and global amalgamation.
-/
class PDCWithDescent (τ : Type u) (Carrier : τ → Type v)
    extends PDCWithTransport τ Carrier where
  MatchingFamily : (∀ t, Carrier t) → Prop
  amalgamate : ∀ x, MatchingFamily x → ∃ g : Plato, ∀ t, fromPlato t g = x t

namespace PDCWithDescent

variable {τ : Type u} {Carrier : τ → Type v} [P : PDCWithDescent τ Carrier]

/-- A matching family has a global amalgamation witness. -/
theorem exists_global (x : ∀ t, Carrier t) (hx : P.MatchingFamily x) :
    ∃ g : P.Plato, ∀ t, P.fromPlato t g = x t :=
  P.amalgamate x hx

/-- Matching families induce a perspective-independent `toPlato` value. -/
theorem toPlato_const (x : ∀ t, Carrier t) (hx : P.MatchingFamily x) :
    ∃ g : P.Plato, ∀ t, P.toPlato t (x t) = g := by
  rcases P.amalgamate x hx with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  intro t
  calc
    P.toPlato t (x t) = P.toPlato t (P.fromPlato t g) := by rw [hg t]
    _ = g := P.rt2 t g

end PDCWithDescent

end Embeddings
end HeytingLean
