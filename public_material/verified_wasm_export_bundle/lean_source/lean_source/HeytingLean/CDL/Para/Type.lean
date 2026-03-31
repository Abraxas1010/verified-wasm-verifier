import Mathlib.CategoryTheory.Iso

/-!
# CDL: `Para(Type)` (cartesian case)

This file implements the *cartesian* instance of the parametric category `Para(C)` used in
Categorical Deep Learning (CDL):

- base category `C := Type`,
- parameter category `M := Type` with tensor `⊗ := Prod` and unit `𝟙 := PUnit`,
- action `⊲ := Prod`.

In this specialization:

- a 1-morphism `X ⟶ Y` is a parameter type `P` and a map `P × X → Y`,
- a 2-morphism is a **reparameterization** `r : P' → P` commuting with the maps.

We deliberately implement just the Lean-realistic spine (1-cells, 2-cells, and coherence isos)
needed for weight-tying proofs and examples, without committing to Mathlib’s full `Bicategory`
interface yet.
-/

namespace HeytingLean
namespace CDL
namespace Para

universe u

/-! ## 1-cells: parametric maps -/

/-- A parametric map `X ⟶ Y` with parameter type `P` and semantics `P × X → Y`. -/
structure ParaHom (X Y : Type u) : Type (u + 1) where
  P : Type u
  f : P × X → Y

namespace ParaHom

variable {W X Y Z : Type u}

/-- Identity 1-cell. -/
def id (X : Type u) : ParaHom X X :=
  ⟨PUnit, fun | (⟨⟩, x) => x⟩

/-- Composition of 1-cells; stacks parameters by product. -/
def comp (g : ParaHom Y Z) (f : ParaHom X Y) : ParaHom X Z :=
  ⟨g.P × f.P, fun | ((pg, pf), x) => g.f (pg, f.f (pf, x))⟩

@[simp] theorem id_P (X : Type u) : (id X).P = PUnit := rfl
@[simp] theorem comp_P (g : ParaHom Y Z) (f : ParaHom X Y) : (comp g f).P = (g.P × f.P) := rfl

/-- Reparameterize a parametric map along `r : P' → P`. -/
def reparam (m : ParaHom X Y) {P' : Type u} (r : P' → m.P) : ParaHom X Y :=
  ⟨P', fun | (p', x) => m.f (r p', x)⟩

end ParaHom

/-! ## 2-cells: reparameterizations -/

/-- A 2-morphism `(P,f) ⇒ (P',f')` is a reparameterization `r : P' → P` commuting with the maps. -/
structure Para2Hom {X Y : Type u} (f g : ParaHom X Y) : Type (u + 1) where
  r : g.P → f.P
  comm : ∀ (p : g.P) (x : X), g.f (p, x) = f.f (r p, x)

namespace Para2Hom

variable {X Y Z : Type u}
variable {f g h : ParaHom X Y}

@[ext] theorem ext {α β : Para2Hom f g} (hr : α.r = β.r) : α = β := by
  cases α with
  | mk rα cα =>
    cases β with
    | mk rβ cβ =>
      cases hr
      rfl

/-- Identity 2-morphism. -/
def refl (f : ParaHom X Y) : Para2Hom f f :=
  ⟨id, by intro p x; rfl⟩

/-- Vertical composition of 2-morphisms (composition of reparameterizations). -/
def vcomp (α : Para2Hom f g) (β : Para2Hom g h) : Para2Hom f h :=
  ⟨α.r ∘ β.r, by
    intro p x
    simpa [Function.comp] using (β.comm p x).trans (α.comm (β.r p) x)⟩

@[simp] theorem refl_r (f : ParaHom X Y) : (refl f).r = id := rfl
@[simp] theorem vcomp_r (α : Para2Hom f g) (β : Para2Hom g h) : (vcomp α β).r = α.r ∘ β.r := rfl

/-- Reparameterization witness for `ParaHom.reparam`. -/
def reparam {X Y : Type u} (m : ParaHom X Y) {P' : Type u} (r : P' → m.P) :
    Para2Hom m (ParaHom.reparam m r) :=
  ⟨r, by intro p x; rfl⟩

variable {W : Type u}
variable {f₁ f₂ : ParaHom W X} {g₁ g₂ : ParaHom X Y}

/-- Horizontal composition of 2-morphisms (acts on product parameters). -/
def hcomp (α : Para2Hom f₁ f₂) (β : Para2Hom g₁ g₂) :
    Para2Hom (ParaHom.comp g₁ f₁) (ParaHom.comp g₂ f₂) :=
  ⟨fun p => (β.r p.1, α.r p.2), by
    intro p w
    -- `β` transports the outer application, `α` transports the inner application.
    have hα : f₂.f (p.2, w) = f₁.f (α.r p.2, w) := α.comm p.2 w
    have hβ : g₂.f (p.1, f₂.f (p.2, w)) = g₁.f (β.r p.1, f₂.f (p.2, w)) :=
      β.comm p.1 (f₂.f (p.2, w))
    -- combine and reduce
    simpa [ParaHom.comp, hα] using hβ⟩

end Para2Hom

/-! ## Hom categories (vertical composition) -/

open CategoryTheory

instance (X Y : Type u) : Category (ParaHom X Y) where
  Hom f g := Para2Hom f g
  id f := Para2Hom.refl f
  comp α β := Para2Hom.vcomp α β
  id_comp := by
    intro f g α
    ext p
    rfl
  comp_id := by
    intro f g α
    ext p
    rfl
  assoc := by
    intro f g h i α β γ
    ext p
    rfl

/-! ## Standard coherence isomorphisms (unitors/associator) -/

namespace Coherence

variable {X Y Z W : Type u}

def leftUnitor (f : ParaHom X Y) : ParaHom.comp (ParaHom.id Y) f ≅ f where
  hom := ⟨fun p => (⟨⟩, p), by intro p x; rfl⟩
  inv := ⟨fun p => p.2, by intro p x; cases p with | mk u p => cases u; rfl⟩
  hom_inv_id := by
    apply Para2Hom.ext
    rfl
  inv_hom_id := by
    apply Para2Hom.ext
    rfl

def rightUnitor (f : ParaHom X Y) : ParaHom.comp f (ParaHom.id X) ≅ f where
  hom := ⟨fun p => (p, ⟨⟩), by intro p x; rfl⟩
  inv := ⟨fun p => p.1, by intro p x; cases p with | mk p u => cases u; rfl⟩
  hom_inv_id := by
    apply Para2Hom.ext
    rfl
  inv_hom_id := by
    apply Para2Hom.ext
    rfl

def assoc (h : ParaHom Y Z) (g : ParaHom X Y) (f : ParaHom W X) :
    ParaHom.comp h (ParaHom.comp g f) ≅ ParaHom.comp (ParaHom.comp h g) f where
  hom := ⟨fun p => (p.1.1, (p.1.2, p.2)), by intro p x; rfl⟩
  inv := ⟨fun p => ((p.1, p.2.1), p.2.2), by intro p x; rfl⟩
  hom_inv_id := by
    apply Para2Hom.ext
    funext p
    cases p with
    | mk pH pGF =>
      cases pGF with
      | mk pG pF =>
        rfl
  inv_hom_id := by
    apply Para2Hom.ext
    funext p
    cases p with
    | mk pHG pF =>
      cases pHG with
      | mk pH pG =>
        rfl

end Coherence

end Para
end CDL
end HeytingLean
