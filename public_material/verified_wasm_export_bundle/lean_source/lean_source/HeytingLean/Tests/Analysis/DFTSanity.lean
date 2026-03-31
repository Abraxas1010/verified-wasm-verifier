import HeytingLean.Analysis.FourierCore
import HeytingLean.Analysis.DFT

open HeytingLean.Analysis
open Complex

namespace HeytingLean
namespace Tests
namespace Analysis

/-!
# Sanity checks for Complex DFT (compile-time only)

Compile-only sanity examples; no `#eval` to keep strict builds stable.
-/

-- N = 2: constant vector and delta
def const2 : Array ℂ := #[(1 : ℂ), 1]
def delta2 : Array ℂ := #[(1 : ℂ), 0]
-- Round-trip sample
def x4 : Array ℂ := #[(1 : ℂ), 0, -1, 0]

-- Band projector idempotence (functional form)
example :
    let N := 4
    let Ω : Fin N → Prop := fun k => k.val < 2
    let X : Fin N → ℂ := fun k => (k.val : ℂ)
    bandProjector Ω (bandProjector Ω X) = bandProjector Ω X := by
  intro N Ω X; simpa using bandProjector_idem (Ω := Ω) X

/-!
N=4 convolution sanity (compile-only):
We wire the expressions to ensure API stability without runtime evaluation.
-/

noncomputable def conv_demo_spec : Array ℂ :=
  let x : Array ℂ := #[(1 : ℂ), 0, -1, 0]
  let y : Array ℂ := #[(0 : ℂ), 1, 0, -1]
  let X := dftArray x
  let Y := dftArray y
  let conv_xy := circConvArray x y
  let lhs := dftArray conv_xy
  let rhs := pointwiseMul X Y
  -- return concatenation to keep the compiler building both branches
  lhs ++ rhs

end Analysis
end Tests
end HeytingLean
