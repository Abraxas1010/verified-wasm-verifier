import HeytingLean.Physics.SpinGlass.Model
import HeytingLean.Physics.SpinGlass.Phase
import HeytingLean.Physics.SpinGlass.Identities
import HeytingLean.Logic.PSR.Robustness

/-
# Chaos & Reentrance lens — spec-level predicates

This module connects the correlated-disorder spin-glass model to
abstract predicates for temperature chaos and reentrance.  It is
intended as the logical backbone for the Chaos & Reentrance lens:

* `TempChaos` describes when an overlap distribution is concentrated
  near zero (temperature chaos),
* `ReentrantEA` (from `SpinGlass.Phase`) captures FM → non-FM → FM
  behaviour along the EA plane, and
* `reentrance_implies_chaos_or_noSG` encodes, as a lens-local law,
  the logical consequence "reentrance ⇒ temperature chaos or no
  spin-glass phase" drawn from Nishimori–Ohzeki–Okuyama.

No physics is re-proved here; the emphasis is on providing precise
predicates for contracts and verifiers.
-/

namespace HeytingLean
namespace Physics
namespace SpinGlass

open SpinGlass
open HeytingLean.Logic

/-- A simple notion of temperature chaos: the overlap distribution
is concentrated near zero up to a tolerance `ε`.

This definition is intentionally lightweight: it treats the distribution as a
finite histogram and checks that any bin with nonzero mass lies within `[-ε, ε]`.
-/
def TempChaos (ov : Dist) (ε : ℝ) : Prop :=
  ∀ xm ∈ List.zip ov.bins ov.mass, xm.snd ≠ 0 → |xm.fst| ≤ ε

/--
Lens-local logical laws for the Chaos & Reentrance lens.

These are packaged as an explicit assumption record (rather than global declarations)
so downstream code remains parametric and the core library stays lightweight.
-/
structure Laws : Type where
  /-- A (lens-local) predicate asserting whether a spin-glass phase exists. -/
  SG_exists : Prop

  /-- Logical law: reentrance ⇒ temperature chaos or no spin-glass phase. -/
  reentrance_implies_chaos_or_noSG :
      ∀ (curve : List BoundarySample) (ov : Dist) (ε : ℝ),
        ReentrantEA curve → TempChaos ov ε ∨ ¬ SG_exists

namespace Toy

/-!
Toy instantiation: declare no spin-glass phase (`SG_exists := False`), so the
reentrance⇒chaos-or-noSG law holds trivially. This keeps the API exercised without
introducing global axioms.
-/

def laws : Laws where
  SG_exists := False
  reentrance_implies_chaos_or_noSG := by
    intro _ _ _ _
    exact Or.inr (by intro h; cases h)

end Toy

end SpinGlass
end Physics
end HeytingLean
