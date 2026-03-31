import HeytingLean.Coalgebra.Universal.Core
import HeytingLean.Coalgebra.Universal.Lattice

/-!
# Universal coalgebra (Type) — bisimulation

We provide two complementary notions:

1. **Span bisimulation** (Rutten-style): a coalgebra `R` together with coalgebra morphisms
   `R ⟶ S` and `R ⟶ T`. This makes sense for any endofunctor on any category.

2. **Relation bisimulation** (Type-only): for endofunctors on `Type` equipped with a relator
   (`LiftR`), we define “bisimilarity” as the greatest fixed point of the usual relation
   transformer.

The span-based notion is useful for categorical statements; the relation-based notion is what we
use in executable examples (streams, automata).
-/

namespace HeytingLean
namespace Coalgebra
namespace Universal

open CategoryTheory

universe u

/-! ## Span bisimulations -/

namespace Span

variable {F : Type u ⥤ Type u}

/-- A bisimulation span between coalgebras `S` and `T`. -/
structure Bisimulation (S T : Universal.Coalg (F := F)) where
  R : Universal.Coalg (F := F)
  left : R ⟶ S
  right : R ⟶ T

/-- The induced binary relation of a bisimulation span. -/
def Bisimulation.Rel {S T : Universal.Coalg (F := F)} (B : Bisimulation (F := F) S T) :
    S.V → T.V → Prop :=
  fun s t => ∃ r : B.R.V, B.left.f r = s ∧ B.right.f r = t

/-- The graph of a coalgebra morphism is a bisimulation span. -/
def graph {S T : Universal.Coalg (F := F)} (f : S ⟶ T) : Bisimulation (F := F) S T where
  R := S
  left := 𝟙 S
  right := f

theorem graph_rel {S T : Universal.Coalg (F := F)} (f : S ⟶ T) (s : S.V) :
    (graph (F := F) f).Rel s (f.f s) := by
  refine ⟨s, ?_, ?_⟩
  · rfl
  · rfl

end Span

/-! ## Relation bisimulations via relators -/

/-- A relator (`LiftR`) for an endofunctor `F` on `Type`.

This is the minimum structure needed to talk about relation-lifting and bisimulation.
-/
class Relator (F : Type u ⥤ Type u) where
  /-- Lift a relation `R : α → β → Prop` to a relation on `F α` and `F β`. -/
  LiftR : {α β : Type u} → (α → β → Prop) → F.obj α → F.obj β → Prop
  /-- Monotonicity of `LiftR` in the relation argument. -/
  mono :
    ∀ {α β : Type u} {R S : α → β → Prop},
      (∀ a b, R a b → S a b) →
      ∀ x y, LiftR R x y → LiftR S x y

namespace Relator

variable {F : Type u ⥤ Type u} [Relator F]

theorem liftR_mono {α β : Type u} {R S : α → β → Prop}
    (h : ∀ a b, R a b → S a b) :
    ∀ x y, Relator.LiftR (F := F) R x y → Relator.LiftR (F := F) S x y :=
  Relator.mono h

end Relator

namespace RelBisim

variable {F : Type u ⥤ Type u} [Relator F]

/-- One-step relation transformer for coalgebras `S` and `T`. -/
def Step (S T : Universal.Coalg (F := F)) : Rel S.V T.V → Rel S.V T.V :=
  fun R s t => Relator.LiftR (F := F) R (S.str s) (T.str t)

theorem step_monotone (S T : Universal.Coalg (F := F)) : RelMonotone (Step (F := F) S T) := by
  intro R S hRS s t
  exact Relator.liftR_mono (F := F) hRS _ _

/-- A relation `R` is a bisimulation if it is post-fixed for the step transformer. -/
def IsBisimulation (S T : Universal.Coalg (F := F)) (R : Rel S.V T.V) : Prop :=
  PostFixed (Step (F := F) S T) R

/-- The greatest bisimulation (bisimilarity), defined as the gfp of `Step`. -/
def Bisimilar (S T : Universal.Coalg (F := F)) : Rel S.V T.V :=
  gfp (Step (F := F) S T)

theorem bisimilar_isBisimulation (S T : Universal.Coalg (F := F)) :
    IsBisimulation (F := F) S T (Bisimilar (F := F) S T) :=
  gfp_postFixed (Φ := Step (F := F) S T) (step_monotone (F := F) S T)

/-- Coinduction: any bisimulation relation is contained in bisimilarity. -/
theorem coinduction {S T : Universal.Coalg (F := F)} {R : Rel S.V T.V}
    (hR : IsBisimulation (F := F) S T R) :
    R ≤ᵣ Bisimilar (F := F) S T :=
  gfp_isGreatest (Φ := Step (F := F) S T) hR

end RelBisim

end Universal
end Coalgebra
end HeytingLean
