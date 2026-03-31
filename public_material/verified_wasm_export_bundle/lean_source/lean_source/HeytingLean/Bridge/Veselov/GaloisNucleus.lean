import Mathlib.Order.Nucleus
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.FieldTheory.Finite.Basic

/-!
# Bridge.Veselov.GaloisNucleus

Constructive P1 bridge surface:
- modules over finite fields (including characteristic-2 lanes),
- nucleus on powerset lattices,
- linear-map compatibility.
-/

namespace HeytingLean.Bridge.Veselov

universe u v w

/-- Module-induced closure nucleus on `Set V` (adds the zero vector). -/
def moduleZeroNucleus
    (F : Type u) (V : Type v)
    [Field F] [AddCommGroup V] [Module F V] :
    Nucleus (Set V) where
  toInfHom :=
    { toFun := fun S => S ∪ ({0} : Set V)
      map_inf' := by
        intro A B
        ext x
        constructor
        · intro hx
          rcases hx with hx | hx
          · exact ⟨Or.inl hx.1, Or.inl hx.2⟩
          · exact ⟨Or.inr hx, Or.inr hx⟩
        · intro hx
          rcases hx with ⟨hxA, hxB⟩
          rcases hxA with hxA | hxA
          · rcases hxB with hxB | hxB
            · exact Or.inl ⟨hxA, hxB⟩
            · exact Or.inr hxB
          · exact Or.inr hxA }
  idempotent' := by
    intro S
    intro x hx
    simp at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx
  le_apply' := by
    intro S
    intro x hx
    exact Or.inl hx

@[simp] theorem moduleZeroNucleus_apply
    (F : Type u) (V : Type v)
    [Field F] [AddCommGroup V] [Module F V]
    (S : Set V) :
    moduleZeroNucleus F V S = S ∪ ({0} : Set V) := rfl

/-- Linear maps preserve the `moduleZeroNucleus` closure relation. -/
theorem moduleZeroNucleus_map_image
    (F : Type u) (V : Type v) (W : Type w)
    [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (f : V →ₗ[F] W)
    (S : Set V) :
    f '' (moduleZeroNucleus F V S) ⊆ moduleZeroNucleus F W (f '' S) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  rcases hx with hx | hx
  · exact Or.inl ⟨x, hx, rfl⟩
  · right
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    simp

/-- P1 object-level bridge: any characteristic-2 finite-field module induces a powerset nucleus. -/
theorem gf2n_module_has_nucleus
    (F : Type u) (V : Type v)
    [Field F] [Fintype F] [CharP F 2]
    [AddCommGroup V] [Module F V] :
    ∃ _J : Nucleus (Set V), True :=
  ⟨moduleZeroNucleus F V, trivial⟩

/-- Functorial composition form of the image-compatibility law. -/
theorem moduleZeroNucleus_map_image_comp
    (F : Type u) (V : Type v) (W : Type w) (U : Type _)
    [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    [AddCommGroup U] [Module F U]
    (f : V →ₗ[F] W) (g : W →ₗ[F] U)
    (S : Set V) :
    (g ∘ₗ f) '' (moduleZeroNucleus F V S)
      ⊆ moduleZeroNucleus F U ((g ∘ₗ f) '' S) := by
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  rcases hx with hx | hx
  · exact Or.inl ⟨x, hx, rfl⟩
  · right
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    simp

/-- Subsets that explicitly contain the zero vector. -/
def zeroClosedSubsets (V : Type v) [Zero V] : Type v :=
  { S : Set V // (0 : V) ∈ S }

/-- Fixed-point characterization for the module-zero nucleus. -/
theorem moduleZeroNucleus_fixed_iff_zero_mem
    (F : Type u) (V : Type v)
    [Field F] [AddCommGroup V] [Module F V]
    (S : Set V) :
    moduleZeroNucleus F V S = S ↔ (0 : V) ∈ S := by
  constructor
  · intro hfix
    have h0 : (0 : V) ∈ moduleZeroNucleus F V S := by
      simp [moduleZeroNucleus]
    simpa [hfix] using h0
  · intro h0
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact hx
      · have hx0 : x = 0 := by simpa using hx
        simpa [hx0] using h0
    · intro hx
      exact Or.inl hx

/--
Global correspondence equivalence:
module-zero nucleus fixed points are exactly zero-closed subsets.
-/
def moduleZeroFixedEquivZeroClosed
    (F : Type u) (V : Type v)
    [Field F] [AddCommGroup V] [Module F V] :
    { S : Set V // moduleZeroNucleus F V S = S } ≃ zeroClosedSubsets V where
  toFun := fun S =>
    ⟨S.1, (moduleZeroNucleus_fixed_iff_zero_mem (F := F) (V := V) S.1).1 S.2⟩
  invFun := fun S =>
    ⟨S.1, (moduleZeroNucleus_fixed_iff_zero_mem (F := F) (V := V) S.1).2 S.2⟩
  left_inv := by
    intro S
    apply Subtype.ext
    rfl
  right_inv := by
    intro S
    apply Subtype.ext
    rfl

/--
Scoped P1 closure theorem (finite class):
for finite characteristic-2 modules, the canonical closure nucleus is explicit and
compatible with linear-map image transport.
-/
theorem p1_finite_class_bridge
    (F : Type u) (V : Type v) (W : Type w)
    [Field F] [Fintype F] [CharP F 2]
    [AddCommGroup V] [Module F V] [Fintype V]
    [AddCommGroup W] [Module F W]
    (f : V →ₗ[F] W) :
    ∃ J : Nucleus (Set V),
      (∀ S : Set V, J S = S ∪ ({0} : Set V)) ∧
      (∀ S : Set V, f '' (J S) ⊆ moduleZeroNucleus F W (f '' S)) := by
  refine ⟨moduleZeroNucleus F V, ?_, ?_⟩
  · intro S
    rfl
  · intro S
    exact moduleZeroNucleus_map_image F V W f S

/--
Canonical c08 correspondence surface:
in characteristic-2 finite-field lanes, fixed points of the module-zero nucleus
globally coincide with zero-closed subsets.
-/
theorem lof_gf2_correspondence_global
    (F : Type u) (V : Type v)
    [Field F] [Fintype F] [CharP F 2]
    [AddCommGroup V] [Module F V] :
    Nonempty ({ S : Set V // moduleZeroNucleus F V S = S } ≃ zeroClosedSubsets V) := by
  exact ⟨moduleZeroFixedEquivZeroClosed (F := F) (V := V)⟩

end HeytingLean.Bridge.Veselov
