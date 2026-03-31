import Mathlib.Data.Fintype.Order
import Mathlib.Data.Set.Lattice
import HeytingLean.LoF.ComparisonNucleus.Soundness

/-
Small concrete examples of `CompSpec` and their fixed-point cores.

We currently expose two deliberately minimal examples:
- `boolCompSpec` on `Bool`, and
- `fin2CompSpec` on the four-element Boolean lattice `Set (Fin 2)`.

Both use identity comparison maps, so `ΩR` is isomorphic to the
underlying lattice in each case. These provide tiny but explicit
windows for instantiating generic lemmas (e.g. in the SKY bridge or
multiway semantics).
-/

namespace HeytingLean
namespace LoF
namespace Comparison

open scoped Classical

/-- A trivial comparison specification on `Bool`: both comparison maps
are the identity.  The Galois connection is therefore tautological. -/
noncomputable def boolCompSpec : CompSpec Bool Bool :=
{ f := id
  g := id
  mon_f := by
    intro x y hxy
    simpa using hxy
  mon_g := by
    intro x y hxy
    simpa using hxy
  gc := by
    intro x y
    constructor <;> intro h <;> simpa using h }

/-- The fixed-point core `ΩR` for `boolCompSpec` is isomorphic to
`Bool`.  Since `act` is just the identity, every Boolean is already a
fixed point. -/
noncomputable def boolΩREquiv : ΩR boolCompSpec ≃ Bool :=
{ toFun := fun a => a.val
  invFun := fun b =>
    ⟨b, by
      -- `act` is `id`, so every element is a fixed point.
      simp [act, boolCompSpec]⟩
  left_inv := by
    intro a
    cases a with
    | mk b hb =>
      -- Equality of subtypes reduces to equality of carriers.
      apply Subtype.ext
      rfl
  right_inv := by
    intro b
    -- By definition `toFun` just projects the underlying Bool.
    rfl }

/-- A slightly richer finite example: identity comparison on the
four-element Boolean lattice `Set (Fin 2)`. -/
noncomputable def fin2CompSpec : CompSpec (Set (Fin 2)) (Set (Fin 2)) :=
{ f := id
  g := id
  mon_f := by
    intro x y hxy
    simpa using hxy
  mon_g := by
    intro x y hxy
    simpa using hxy
  gc := by
    intro x y
    constructor <;> intro h <;> simpa using h }

/-- The fixed-point core `ΩR` for `fin2CompSpec` is isomorphic to
`Set (Fin 2)`.  Again, `act` is just the identity, so every set is a
fixed point. -/
noncomputable def fin2ΩREquiv : ΩR fin2CompSpec ≃ Set (Fin 2) :=
{ toFun := fun a => a.val
  invFun := fun s =>
    ⟨s, by
      -- `act` is `id`, so every element is a fixed point.
      simp [act, fin2CompSpec]⟩
  left_inv := by
    intro a
    cases a with
    | mk s hs =>
      -- Equality of subtypes reduces to equality of carriers.
      apply Subtype.ext
      rfl
  right_inv := by
    intro s
    -- By definition `toFun` just projects the underlying set.
    rfl }

end Comparison
end LoF
end HeytingLean
