import HeytingLean.CDL.Para.Type

/-!
# CDL: strong monads (Type/cartesian case) and the `Para(T)` lift

CDL (Gavranović et al., arXiv:2402.15332v2) lifts a (strong) monad `T` on a base category `C`
to a 2-monad `Para(T)` on the parametric 2-category `Para(C)`.

For this repo’s Lean-realistic scope we:

- define a minimal `StrongMonad` interface on `Type`,
- implement the induced action on parametric maps `ParaHom`,
- provide the key “sanity” lemmas: identity/comp preservation **up to reparameterization**
  (assuming `LawfulMonad` for the functor laws).

We start in the cartesian case `C := Type` where a canonical product-strength exists.
-/

namespace HeytingLean
namespace CDL

universe u

/-- A strong monad on `Type u`: a monad equipped with a strength for products. -/
class StrongMonad (T : Type u → Type u) : Type (u + 1) extends Monad T where
  strength : ∀ {P X : Type u}, P × T X → T (P × X)

namespace StrongMonad

variable (T : Type u → Type u)

/-- Canonical cartesian strength for any functor: `P × T X → T (P × X)` by mapping pairing. -/
def canonicalStrength [Functor T] : ∀ {P X : Type u}, P × T X → T (P × X)
  | _, _, (p, tx) => Functor.map (fun x => (p, x)) tx

end StrongMonad

-- In `Type`, every monad admits the canonical cartesian strength.
instance (priority := 100) (T : Type u → Type u) [Monad T] : StrongMonad T where
  toMonad := inferInstance
  strength := StrongMonad.canonicalStrength (T := T)

namespace Para

open HeytingLean.CDL.Para

variable {T : Type u → Type u} [StrongMonad T]

/-- Lift a parametric map through the monad `T` (CDL Example G.8, specialized to `Type`). -/
def map {X Y : Type u} (m : ParaHom X Y) : ParaHom (T X) (T Y) :=
  ⟨m.P, fun | (p, tx) => Functor.map (fun x => m.f (p, x)) tx⟩

/-- Lift a reparameterization through `Para.map`. -/
def map₂ {X Y : Type u} {m m' : ParaHom X Y} (α : Para2Hom m m') :
    Para2Hom (map (T := T) m) (map (T := T) m') :=
  ⟨α.r, by
    intro p tx
    have hfun : (fun x => m'.f (p, x)) = (fun x => m.f (α.r p, x)) := by
      funext x
      exact α.comm p x
    simpa [map] using congrArg (fun k => Functor.map k tx) hfun⟩

/-- The unit of the lifted monad, as a parametric map with trivial parameter. -/
def unit (X : Type u) : ParaHom X (T X) :=
  ⟨PUnit, fun | (⟨⟩, x) => pure x⟩

/-- The multiplication of the lifted monad, as a parametric map with trivial parameter. -/
def mult (X : Type u) : ParaHom (T (T X)) (T X) :=
  ⟨PUnit, fun | (⟨⟩, ttx) => ttx >>= id⟩

/-! ## Functoriality checks (requires functor laws) -/

variable [LawfulMonad T]

def map_id (X : Type u) :
    Para2Hom (map (T := T) (ParaHom.id X)) (ParaHom.id (T X)) := by
  refine ⟨id, ?_⟩
  intro p tx
  cases p
  -- `id <$> tx = tx`
  simp [map, ParaHom.id]

def map_comp {X Y Z : Type u} (g : ParaHom Y Z) (f : ParaHom X Y) :
    Para2Hom (map (T := T) (ParaHom.comp g f))
      (ParaHom.comp (map (T := T) g) (map (T := T) f)) := by
  refine ⟨id, ?_⟩
  intro p tx
  -- `(h ∘ g) <$> tx = h <$> g <$> tx`
  simp [map, ParaHom.comp]

end Para

end CDL
end HeytingLean
