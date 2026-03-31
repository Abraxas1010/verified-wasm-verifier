/-
Copyright (c) 2026 Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/
import Mathlib.RingTheory.Nilpotent.Exp

/-!
# Nilpotent Exponential (Topology-Free)

Mathlib provides a topology-free exponential map `IsNilpotent.exp` on `ℚ`-modules.
This file re-exports the key group-like laws we want for the SurrealLie stack:

- `exp_add_of_commute` for commuting nilpotent elements
- `exp a * exp (-a) = 1` and `IsUnit (exp a)` for nilpotent `a`

These results are the backbone of the "exact microscope" narrative in nilpotent
regimes: the exponential is a finite sum and behaves like the usual exp.
-/

set_option autoImplicit false

namespace HeytingLean.SurrealLie

namespace NilpotentExp

open IsNilpotent

variable {A : Type*} [Ring A] [Module ℚ A]

noncomputable abbrev exp (a : A) : A := IsNilpotent.exp a

theorem exp_add_of_commute {a b : A} (hcomm : Commute a b) (ha : IsNilpotent a) (hb : IsNilpotent b) :
    exp (a + b) = exp a * exp b :=
  IsNilpotent.exp_add_of_commute hcomm ha hb

theorem exp_mul_exp_neg_eq_one {a : A} (ha : IsNilpotent a) :
    exp a * exp (-a) = 1 :=
  IsNilpotent.exp_mul_exp_neg_self ha

theorem exp_neg_mul_exp_eq_one {a : A} (ha : IsNilpotent a) :
    exp (-a) * exp a = 1 :=
  IsNilpotent.exp_neg_mul_exp_self ha

theorem isUnit_exp {a : A} (ha : IsNilpotent a) : IsUnit (exp a) :=
  IsNilpotent.isUnit_exp ha

end NilpotentExp

end HeytingLean.SurrealLie
