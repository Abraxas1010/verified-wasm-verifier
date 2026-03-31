import HeytingLean.LoF.Combinators.Category.BranchialCategory

/-!
# LoF.Combinators.Category.NeuralCategory

Lightweight “categorical deep learning” scaffolding: parametric morphisms and compositional layers.

This is currently a small interface slice intended for later refinement and connection to the
existing categorical infrastructure in `HeytingLean.LoF.Combinators.Category.*`.
-/

namespace HeytingLean
namespace LoF
namespace Combinators
namespace Category

/-- A parametric category: morphisms carry a parameter index, with additive composition of parameters. -/
structure ParaCategory where
  Obj : Type*
  Param : Type*
  [instParam : AddMonoid Param]
  Hom : Obj → Obj → Param → Type*
  id : ∀ A, Hom A A 0
  comp : ∀ {A B C p q}, Hom A B p → Hom B C q → Hom A C (p + q)

/-- A neural network layer as a parametric map with a backward pass. -/
structure NeuralLayer (input output : Type*) (param : Type*) where
  forward : input → param → output
  backward : input → param → output → (input × param)

/-- Composition of neural layers. -/
def NeuralLayer.compose {A B C P Q : Type*}
    (f : NeuralLayer A B P) (g : NeuralLayer B C Q) :
    NeuralLayer A C (P × Q) where
  forward := fun a (p, q) => g.forward (f.forward a p) q
  backward := fun a (p, q) dc =>
    let (db, dq) := g.backward (f.forward a p) q dc
    let (da, dp) := f.backward a p db
    (da, (dp, dq))

/-- Functoriality: structure-preserving map between parametric categories. -/
structure NeuralFunctor (F G : ParaCategory) where
  objMap : F.Obj → G.Obj
  paramMap : F.Param → G.Param
  homMap : ∀ {A B p}, F.Hom A B p → G.Hom (objMap A) (objMap B) (paramMap p)
  comp_preserving :
    ∀ {A B C p q} (f : F.Hom A B p) (g : F.Hom B C q),
      HEq (homMap (F.comp f g)) (G.comp (homMap f) (homMap g))

/-- Forward pass of composed layers is by definition nested composition. -/
@[simp] theorem backprop_forward_compose {A B C P Q : Type*}
    (f : NeuralLayer A B P) (g : NeuralLayer B C Q)
    (a : A) (p : P) (q : Q) :
    (NeuralLayer.compose f g).forward a (p, q) = g.forward (f.forward a p) q := rfl

/-- Restricted chain-rule shape: the composed backward pass factors through the intermediate pullback. -/
theorem backprop_compose_chain {A B C P Q : Type*}
    (f : NeuralLayer A B P) (g : NeuralLayer B C Q)
    (a : A) (p : P) (q : Q) (dc : C) :
    let (db, dq) := g.backward (f.forward a p) q dc
    let (da, dp) := f.backward a p db
    (NeuralLayer.compose f g).backward a (p, q) dc = (da, (dp, dq)) := by
  rfl

end Category
end Combinators
end LoF
end HeytingLean
