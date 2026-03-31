/-
Copyright (c) 2026 Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/
import HeytingLean.SurrealLie.FormalExpLog
import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Nilpotent Matrix Prototypes

This module provides simple, topology-free exp/log prototypes for nilpotent-style
matrix settings. The goal is an "exact microscope" demo: in nilpotent regimes,
exponential and logarithm reduce to finite polynomials, so no analytic convergence
machinery is required.

This file intentionally stays lightweight: it defines the relevant predicates and
the polynomial exp/log maps on matrices, but does not build a full Lie group API.
-/

set_option autoImplicit false

open scoped BigOperators Matrix

namespace HeytingLean.SurrealLie

/-! ### Strict Upper Triangular Matrices -/

variable {𝕜 : Type*} [Zero 𝕜]
variable {n : ℕ}

/-- A matrix is strictly upper triangular if all entries on or below the diagonal are zero. -/
def IsStrictUpperTriangular (A : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  ∀ i j : Fin n, j ≤ i → A i j = 0

/-- The subtype of strictly upper triangular matrices. -/
def StrictUpperTriangular (n : ℕ) (𝕜 : Type*) [Zero 𝕜] :=
  { A : Matrix (Fin n) (Fin n) 𝕜 // IsStrictUpperTriangular (n := n) A }

/-! ### Unipotent Matrices -/

section Unipotent

variable {𝕜 : Type*} [Ring 𝕜]
variable {n : ℕ}

/-- A matrix is unipotent if `U - 1` is nilpotent. -/
def IsUnipotent (U : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  IsNilpotent (U - 1)

/-- The subtype of unipotent matrices. -/
def Unipotent (n : ℕ) (𝕜 : Type*) [Ring 𝕜] :=
  { U : Matrix (Fin n) (Fin n) 𝕜 // IsUnipotent (n := n) U }

end Unipotent

/-! ### Polynomial Exp/Log on Matrices -/

section ExpLog

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
variable {n : ℕ}

/-- Truncated matrix exponential (finite polynomial). -/
noncomputable def nilpotentMatrixExp (A : StrictUpperTriangular n 𝕜) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  expPoly 𝕜 (Matrix (Fin n) (Fin n) 𝕜) n A.1

/-- Truncated matrix logarithm around identity (finite polynomial). -/
noncomputable def unipotentMatrixLog (U : Unipotent n 𝕜) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  logPoly 𝕜 (Matrix (Fin n) (Fin n) 𝕜) n U.1

end ExpLog

end HeytingLean.SurrealLie

