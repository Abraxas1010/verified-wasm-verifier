/-
Copyright (c) 2026 Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/
import HeytingLean.SurrealLie.FormalExpLog
import HeytingLean.SurrealLie.NilpotentExp
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Nilpotent Logarithm (Topology-Free)

This file defines a topology-free logarithm on *unipotent* elements of a `ℚ`-algebra,
implemented as a finite truncated series on nilpotent elements.

The goal is to complement `HeytingLean.SurrealLie.NilpotentExp` with the missing
inverse-direction interface needed by the SurrealLie narrative.

This is intentionally scoped to hypotheses where the inverse laws are standard and
auditable in algebraic settings.
-/

set_option autoImplicit false

namespace HeytingLean.SurrealLie

open scoped BigOperators

section

variable {A : Type*} [CommRing A]

namespace NilpotentLog

open HeytingLean.SurrealLie (logPoly expPoly)
open IsNilpotent

/-- A unipotent element is one of the form `1 + n` with `n` nilpotent. -/
structure Unipotent : Type _ where
  val : A
  isUnipotent : ∃ n : A, IsNilpotent n ∧ val = 1 + n

instance : Coe (Unipotent (A := A)) A := ⟨fun u => u.val⟩

/-- The nilpotent part of a unipotent element: `u - 1`. -/
def nilPart (u : Unipotent (A := A)) : A :=
  (u : A) - 1

lemma isNilpotent_nilPart (u : Unipotent (A := A)) : IsNilpotent (nilPart (A := A) u) := by
  rcases u.isUnipotent with ⟨n, hn, hval⟩
  have hnil : nilPart (A := A) u = n := by
    -- `u - 1 = n` when `u = 1 + n`.
    simp [nilPart, hval, add_comm]
  simpa [hnil] using hn

lemma nilPart_pow_nilpotencyClass (u : Unipotent (A := A)) :
    (nilPart (A := A) u) ^ nilpotencyClass (nilPart (A := A) u) = 0 :=
  pow_nilpotencyClass (isNilpotent_nilPart (A := A) u)

/- We only define the logarithm in the `ℚ`-algebra setting. -/
variable [Algebra ℚ A]

/-- Topology-free logarithm on unipotent elements, defined by choosing a nilpotency exponent
for `u - 1` and evaluating `logPoly` at that exponent. -/
noncomputable def log (u : Unipotent (A := A)) : A :=
  -- Use Mathlib's `nilpotencyClass` to select a canonical exponent.
  logPoly ℚ A (nilpotencyClass (nilPart (A := A) u) + 1) (u : A)

end NilpotentLog

end

end HeytingLean.SurrealLie
