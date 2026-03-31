import Mathlib.Tactic

namespace HeytingLean.OpenCLAW.Dialectica

universe u

/-!
# Prop-Valued Dialectica Protocol Layer

This module provides a lightweight Prop-valued dialectica structure for protocol
security wrappers.

- source_type: dialectica category theory (de Paiva)
- attribution_status: n/a (categorical infrastructure)
- claim_status: n/a
- proof_status: proved

## Relationship to `Dial C`

`ProtocolLayer` is a Prop-valued specialization of the general dialectica category
`HeytingLean.CategoryTheory.Dialectica.Dial C` (see
`CategoryTheory/Dialectica/Basic.lean`).

Specifically, `ProtocolLayer` corresponds to `Dial (Type u)` where:
- `src` = `Witness`
- `tgt` = `Challenge`
- `rel` = a Prop-valued relation over witness/challenge pairs

The general `Dial C` construction works over any category with finite products
and pullbacks. This module keeps only the Prop-level tensor/unit structure needed
for OpenCLAW integration. The explicit functor into `Dial C` is deferred.
-/

/-- A protocol layer in the dialectica sense: witnesses, challenges, and a security relation. -/
structure ProtocolLayer where
  Witness : Type u
  Challenge : Type u
  secure : Witness -> Challenge -> Prop

/-- A security reduction between protocol layers. -/
structure ProtocolMorphism (X Y : ProtocolLayer.{u}) where
  fwd : X.Witness -> Y.Witness
  bwd : X.Witness -> Y.Challenge -> X.Challenge
  valid : forall w c, X.secure w (bwd w c) -> Y.secure (fwd w) c

/-- Identity protocol morphism. -/
def ProtocolMorphism.id (X : ProtocolLayer.{u}) : ProtocolMorphism X X where
  fwd := fun w => w
  bwd := fun _ c => c
  valid := fun _ _ h => h

/-- Composition of protocol morphisms. -/
def ProtocolMorphism.comp {X Y Z : ProtocolLayer.{u}}
    (f : ProtocolMorphism X Y) (g : ProtocolMorphism Y Z) : ProtocolMorphism X Z where
  fwd := g.fwd ∘ f.fwd
  bwd := fun w c => f.bwd w (g.bwd (f.fwd w) c)
  valid := by
    intro w c h
    exact g.valid (f.fwd w) c (f.valid w (g.bwd (f.fwd w) c) h)

/-- Tensor product of protocol layers. -/
def ProtocolLayer.tensor (X Y : ProtocolLayer.{u}) : ProtocolLayer.{u} where
  Witness := X.Witness × Y.Witness
  Challenge := X.Challenge × Y.Challenge
  secure := fun ⟨w1, w2⟩ ⟨c1, c2⟩ => X.secure w1 c1 ∧ Y.secure w2 c2

/-- Trivial unit protocol layer. -/
def ProtocolLayer.unit : ProtocolLayer.{u} where
  Witness := PUnit.{u+1}
  Challenge := PUnit.{u+1}
  secure := fun _ _ => True

/-- Tensor associativity (up to witness/challenge reassociation). -/
theorem tensor_assoc (X Y Z : ProtocolLayer.{u}) :
    forall w c, (X.tensor (Y.tensor Z)).secure w c ↔
      ((X.tensor Y).tensor Z).secure
        ⟨⟨w.1, w.2.1⟩, w.2.2⟩
        ⟨⟨c.1, c.2.1⟩, c.2.2⟩ := by
  intro w c
  rcases w with ⟨wX, wYZ⟩
  rcases wYZ with ⟨wY, wZ⟩
  rcases c with ⟨cX, cYZ⟩
  rcases cYZ with ⟨cY, cZ⟩
  simp [ProtocolLayer.tensor, and_assoc]

/-- Tensor commutativity (up to witness/challenge swap). -/
theorem tensor_comm (X Y : ProtocolLayer.{u}) :
    forall w c, (X.tensor Y).secure w c ↔
      (Y.tensor X).secure ⟨w.2, w.1⟩ ⟨c.2, c.1⟩ := by
  intro w c
  rcases w with ⟨wX, wY⟩
  rcases c with ⟨cX, cY⟩
  simp [ProtocolLayer.tensor, and_comm]

/-- Left unit law for tensor. -/
theorem tensor_unit_left (X : ProtocolLayer.{u}) :
    forall w c,
      (ProtocolLayer.unit.tensor X).secure ⟨PUnit.unit, w⟩ ⟨PUnit.unit, c⟩ ↔ X.secure w c := by
  intro w c
  simp [ProtocolLayer.tensor, ProtocolLayer.unit]

/-- Right unit law for tensor. -/
theorem tensor_unit_right (X : ProtocolLayer.{u}) :
    forall w c,
      (X.tensor ProtocolLayer.unit).secure ⟨w, PUnit.unit⟩ ⟨c, PUnit.unit⟩ ↔ X.secure w c := by
  intro w c
  simp [ProtocolLayer.tensor, ProtocolLayer.unit]

end HeytingLean.OpenCLAW.Dialectica
