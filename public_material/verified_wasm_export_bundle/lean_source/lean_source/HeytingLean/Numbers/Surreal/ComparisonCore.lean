import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Data.Set.BooleanAlgebra
import HeytingLean.LoF.ClosureCore
import HeytingLean.Numbers.SurrealCore
import HeytingLean.Numbers.Surreal.Nucleus

/-!
# Comparison Core via Galois Connection (Scaffolding)

Given `f ⊣ g` between `Set PreGame` and a complete lattice `Ωₗ`,
define the closure `Rᶜ(S) := g (f S)`. This is an extensive,
monotone, idempotent operator (a `ClosureCore`). It has the meet
sub-distribution `Rᶜ(S ∩ T) ⊆ Rᶜ S ∩ Rᶜ T`. Under stronger
assumptions (e.g. `f` a frame morphism), this upgrades to a true
`Nucleus` with equality on meets.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal

open Set
open HeytingLean.LoF
open HeytingLean.Numbers.SurrealCore

universe u

variable {Ωₗ : Type u} [Preorder Ωₗ]

def comparisonCore (f : Set PreGame → Ωₗ) (g : Ωₗ → Set PreGame)
  (gc : GaloisConnection f g) : ClosureCore (Set PreGame) where
  act S := g (f S)
  monotone := by
    intro S T hST
    exact gc.monotone_u (gc.monotone_l hST)
  le_apply := by
    intro S
    exact (gc S (f S)).mp le_rfl
  idempotent := by
    intro S
    -- g ∘ f is idempotent via `l_u_le` composed with monotone `g`.
    -- We use `l_u_le` in the form `f (g x) ≤ x`.
    have h : f (g (f S)) ≤ f S := gc.l_u_le (f S)
    -- Monotone of g: g (f (g (f S))) ≤ g (f S)
    exact le_antisymm
      (gc.monotone_u h)
      ((gc (g (f S)) (f (g (f S)))).mp le_rfl)

lemma comparison_map_inf_le
  (f : Set PreGame → Ωₗ) (g : Ωₗ → Set PreGame) (gc : GaloisConnection f g)
  (S T : Set PreGame) :
  comparisonCore f g gc (S ∩ T) ⊆
    comparisonCore f g gc S ∩ comparisonCore f g gc T := by
  intro x hx
  -- x ∈ g (f (S ∩ T))
  -- Using monotonicity of f and g with projections `S ∩ T ⊆ S`, `S ∩ T ⊆ T`.
  have hxS : x ∈ g (f S) := by
    have hST : S ∩ T ⊆ S := inter_subset_left
    have hf : f (S ∩ T) ≤ f S := gc.monotone_l hST
    have hg : g (f (S ∩ T)) ≤ g (f S) := gc.monotone_u hf
    exact hg hx
  have hxT : x ∈ g (f T) := by
    have hST : S ∩ T ⊆ T := inter_subset_right
    have hf : f (S ∩ T) ≤ f T := gc.monotone_l hST
    have hg : g (f (S ∩ T)) ≤ g (f T) := gc.monotone_u hf
    exact hg hx
  exact And.intro hxS hxT

abbrev Ω_comp (f : Set PreGame → Ωₗ) (g : Ωₗ → Set PreGame)
  (gc : GaloisConnection f g) : Type _ :=
  (comparisonCore f g gc).Omega

/-! ### Initiality (with fixed-point assumption)

If `cl` is a closure on sets that:
- is extensive/monotone/idempotent, and
- commutes with `f` (so `f (cl S) = f S`), and
- its outputs are fixed by `u ∘ l` (so `g (f (cl S)) = cl S`),

then the comparison closure `g ∘ f` is pointwise ≤ `cl`.
-/

lemma comp_core_le_of_comm_and_fixed
  {Ωₗ : Type u} [Preorder Ωₗ]
  (f : Set PreGame → Ωₗ) (g : Ωₗ → Set PreGame) (gc : GaloisConnection f g)
  (cl : Set PreGame → Set PreGame)
  (_cl_ext : ∀ S, S ≤ cl S)
  (_cl_mono : Monotone cl)
  (_cl_idem : ∀ S, cl (cl S) = cl S)
  (comm : ∀ S, f (cl S) = f S)
  (fixed : ∀ S, g (f (cl S)) = cl S) :
  ∀ S, comparisonCore f g gc S ≤ cl S := by
  intro S
  -- comparisonCore f g gc S = g (f S) ≤ g (f (cl S)) = cl S
  have hf : f S ≤ f (cl S) := by simp [comm S]
  have hmono : g (f S) ≤ g (f (cl S)) := gc.monotone_u hf
  simpa [fixed S] using hmono

end Surreal
end Numbers
end HeytingLean
