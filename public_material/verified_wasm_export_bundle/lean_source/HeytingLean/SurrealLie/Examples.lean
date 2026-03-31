/-
Copyright (c) 2026 Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/
import HeytingLean.SurrealLie.Scale
import HeytingLean.SurrealLie.FormalExpLog
import HeytingLean.SurrealLie.NilpotentMatrix
import HeytingLean.SurrealLie.KernelTrait

/-!
# Surreal Lie Group Examples

This module provides examples demonstrating the scale predicates
(macro/micro/gap) and their interaction with Lie group flows.

## Examples

1. Macro rotations — standard finite transformations
2. Micro rotations — infinitesimal perturbations
3. Gap rotations — infinite transformations (wrapping)

## Theoretical Significance

In a Surreal Lie Group, the Lie algebra provides an "exact microscope"
for infinitesimal structure. Unlike ℝ where infinitesimals are just
a figure of speech, in Surreals they are actual elements.
-/

set_option autoImplicit false

namespace HeytingLean.SurrealLie

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ### Scale Examples -/

section ScaleExamples

variable (ε : 𝕜) (hε : IsInfinitesimal (𝕜 := 𝕜) ε)

/-- Infinitesimals are closed under negation. -/
example : IsInfinitesimal (𝕜 := 𝕜) (-ε) :=
  IsInfinitesimal.neg (𝕜 := 𝕜) hε

/-- Zero is infinitesimal. -/
example : IsInfinitesimal (𝕜 := 𝕜) (0 : 𝕜) :=
  isInfinitesimal_zero (𝕜 := 𝕜)

end ScaleExamples

/-! ### Flow Scale Examples -/

section FlowScaleExamples

/-!
Future work:
`micro_shift_first_order` (a first-order expansion of `expPoly`) is a useful lemma for
the "exact microscope" narrative, but it requires careful algebraic bookkeeping in
the general (noncommutative) setting. The SurrealLie stack keeps the scale predicates
and flow APIs build-clean, and defers this lemma to a dedicated follow-up.
-/

/-- Gap shift: still well-defined.

    Even for infinite `Ω`, `exp(Ω • X)` is a valid group element
    when `X` is nilpotent (the sum is finite).
-/
theorem gap_shift_defined {R : Type*} [Field R] [CharZero R]
    {X : R} {N : ℕ} (Ω : R) :
    expPoly R R N (Ω * X) = ∑ k ∈ Finset.range N, (Nat.factorial k : R)⁻¹ * Ω ^ k * X ^ k := by
  -- Here we use `𝕜 = A = R` so scalar action is multiplication.
  simp [expPoly, smul_eq_mul, mul_pow, mul_assoc, mul_comm]

end FlowScaleExamples

/-! ### Smoke Tests -/

section SmokeTests

example : True := by
  -- Smoke-test that the API surface exists without emitting `#check` info output.
  let _p1 : Prop := IsInfinitesimal (𝕜 := 𝕜) (0 : 𝕜)
  let _p2 : Prop := IsInfinite (𝕜 := 𝕜) (0 : 𝕜)
  let _p3 : Prop := IsMacro (𝕜 := 𝕜) (0 : 𝕜)
  have _h0 : IsInfinitesimal (𝕜 := 𝕜) (0 : 𝕜) := isInfinitesimal_zero (𝕜 := 𝕜)
  have _hneg : IsInfinitesimal (𝕜 := 𝕜) (-(0 : 𝕜)) := IsInfinitesimal.neg (𝕜 := 𝕜) _h0
  let _e : 𝕜 := expPoly 𝕜 𝕜 1 (0 : 𝕜)
  let _l : 𝕜 := logPoly 𝕜 𝕜 1 (1 : 𝕜)
  trivial

end SmokeTests

end HeytingLean.SurrealLie
