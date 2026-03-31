import HeytingLean.LoF.Combinators.Rewriting.LocalConfluence

/-!
# Smoke test: overlap peaks for `StepAt.local_confluence`

This file exercises the “overlap” part of the `StepAt` local confluence proof, including the
duplication cases for `S` and `Y`.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.Comb

open Dir RuleTag

namespace Example

/-! ## `S`-overlap: stepping inside the duplicated argument -/

def x : Comb := .K
def y : Comb := .K
def z : Comb := Comb.app (Comb.app .K .S) .K

def tS : Comb := Comb.app (Comb.app (Comb.app .S x) y) z
def uS : Comb := Comb.app (Comb.app x z) (Comb.app y z)
def vS : Comb := Comb.app (Comb.app (Comb.app .S x) y) .S

def hS_root : tS.StepAt .S [] uS :=
  Comb.StepAt.S_root x y z

def hS_inner : tS.StepAt .K [Dir.R] vS :=
  Comb.StepAt.right (f := Comb.app (Comb.app .S x) y) (Comb.StepAt.K_root .S .K)

example : ∃ w : Comb, Comb.Steps uS w ∧ Comb.Steps vS w :=
  Comb.StepAt.local_confluence hS_root hS_inner

/-! ## `Y`-overlap: stepping inside the duplicated argument -/

def fY : Comb := Comb.app (Comb.app .K .S) .K

def tY : Comb := Comb.app .Y fY
def uY : Comb := Comb.app fY (Comb.app .Y fY)
def vY : Comb := Comb.app .Y .S

def hY_root : tY.StepAt .Y [] uY :=
  Comb.StepAt.Y_root fY

def hY_inner : tY.StepAt .K [Dir.R] vY :=
  Comb.StepAt.right (f := .Y) (Comb.StepAt.K_root .S .K)

example : ∃ w : Comb, Comb.Steps uY w ∧ Comb.Steps vY w :=
  Comb.StepAt.local_confluence hY_root hY_inner

end Example

end LoF
end Tests
end HeytingLean
