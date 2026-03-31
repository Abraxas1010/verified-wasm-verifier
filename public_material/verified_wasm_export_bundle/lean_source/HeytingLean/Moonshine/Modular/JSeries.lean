import HeytingLean.Moonshine.Monster.Constants
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.HahnSeries.Addition
import Mathlib.RingTheory.HahnSeries.Basic

set_option autoImplicit false

namespace HeytingLean.Moonshine.Modular

/-- A convenient alias: Laurent/q-series as Hahn series indexed by `ℤ`. -/
abbrev Laurent (R : Type*) [Zero R] := HahnSeries ℤ R

open scoped BigOperators

/--
A *minimal* formal q-expansion for `J(q)=j(q)-744`, as a Hahn/Laurent series.

We hard-code the coefficients for exponents `-1, 0, 1, 2`:
- `q^{-1}` coefficient is `1`
- `q^{0}` coefficient is `0`
- `q^{1}` coefficient is `196884`
- `q^{2}` coefficient is `21493760`
-/
noncomputable def J_qZ : Laurent ℤ :=
  HahnSeries.single (-1 : ℤ) (1 : ℤ)
    + HahnSeries.single (1 : ℤ) (firstJCoeff : ℤ)
    + HahnSeries.single (2 : ℤ) (secondJCoeff : ℤ)

/-- The same series with complex coefficients. -/
noncomputable def J_q : Laurent ℂ :=
  J_qZ.map (Int.castRingHom ℂ)

/-! Coefficient lemmas for the ℤ-coefficient series -/

lemma coeff_J_qZ_neg1 : (J_qZ.coeff (-1)) = (1 : ℤ) := by
  simp [J_qZ]

lemma coeff_J_qZ_0 : (J_qZ.coeff 0) = (0 : ℤ) := by
  simp [J_qZ]

lemma coeff_J_qZ_1 : (J_qZ.coeff 1) = (firstJCoeff : ℤ) := by
  simp [J_qZ]

lemma coeff_J_qZ_2 : (J_qZ.coeff 2) = (secondJCoeff : ℤ) := by
  simp [J_qZ]

/-! Coefficient lemmas for the ℂ-coefficient series -/

lemma coeff_J_q_neg1 : (J_q.coeff (-1)) = (1 : ℂ) := by
  -- `HahnSeries.map` acts coefficientwise.
  simp [J_q, HahnSeries.map, coeff_J_qZ_neg1]

lemma coeff_J_q_0 : (J_q.coeff 0) = (0 : ℂ) := by
  simp [J_q, HahnSeries.map, coeff_J_qZ_0]

lemma coeff_J_q_1 : (J_q.coeff 1) = (firstJCoeff : ℂ) := by
  simp [J_q, HahnSeries.map, coeff_J_qZ_1]

lemma coeff_J_q_2 : (J_q.coeff 2) = (secondJCoeff : ℂ) := by
  simp [J_q, HahnSeries.map, coeff_J_qZ_2]

end HeytingLean.Moonshine.Modular
