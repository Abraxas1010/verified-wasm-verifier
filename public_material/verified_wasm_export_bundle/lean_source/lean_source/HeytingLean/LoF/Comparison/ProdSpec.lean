import HeytingLean.Numbers.SurrealCore
import HeytingLean.Numbers.Surreal.ClosureReentry
import HeytingLean.Numbers.Surreal.NucleusCore
import HeytingLean.LoF.ComparisonNucleus

/-!
Production Spec scaffold for the comparison nucleus.

This defines a concrete `Spec` using existing repository types so the
comparison selector can be wired in production without introducing new
dependencies. You can refine `L`, `Ωℓ`, `f`, and `g` later.
‑/

namespace HeytingLean
namespace Comparison
namespace Prod

open HeytingLean.Numbers
open HeytingLean.Numbers.SurrealCore
open HeytingLean.Numbers.Surreal

/-! ### Production maps (real, non-identity)

We use the Option‑A nucleus `R_union` with the canonical core `canonicalCore`
to define the comparison maps on the concrete carrier `L := Set PreGame`.

`Ωℓ` is the fixed‑point subtype of `R_union canonicalCore`.
-/

abbrev L   := Set SurrealCore.PreGame

private def R : Order.Nucleus L :=
  -- Core‑union nucleus `S ↦ S ∪ canonicalCore`
  HeytingLean.Numbers.Surreal.R_union (C := canonicalCore)

abbrev Ωℓ := (R).toSublocale

/-- Left leg: close then wrap under `R`. -/
def f : L → Ωℓ :=
  fun S => ⟨ R S, by simpa using (R.idempotent S) ⟩

/-- Right leg: unwrap back to sets (subtype projection). -/
def g : Ωℓ → L := Subtype.val

def SpecProd : HeytingLean.LoF.Comparison.Spec L Ωℓ :=
  { f := f, g := g
    , f_mono := by
        intro S T hST
        -- Monotonicity of f follows from monotonicity of the nucleus R.
        exact (HeytingLean.Numbers.Surreal.R_union_mono (C := canonicalCore)) hST
    , g_mono := by
        intro S T hST
        exact hST
    , gc := by
        -- Galois connection between f and g (closure-subtype projection).
        intro S Ω
        change R S ⊆ Ω ↔ S ⊆ Ω
        constructor
        · intro h s hs
          exact h (R.extensive _ hs)
        · intro h s hs
          exact h hs
    , name := "comparison-prod" }

end Prod
end Comparison
end HeytingLean
