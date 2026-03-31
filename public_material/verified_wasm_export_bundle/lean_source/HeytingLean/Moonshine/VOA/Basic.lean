import Mathlib.Algebra.Vertex.VertexOperator
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

open scoped VertexOperator

namespace HeytingLean.Moonshine.VOA

universe u

/--
Minimal VOA data with normalized mode indexing from `VertexOperator`:
`A[[0]]` is the classical `(-1)`-mode.
-/
structure VOAData where
  V : Type u
  instAddCommGroup : AddCommGroup V
  instModule : Module ℂ V
  Y : V → VertexOperator ℂ V
  vacuum : V
  T : Module.End ℂ V
  lower_trunc :
    ∀ a b : V, ∃ N : ℤ, ∀ n : ℤ, n < N → (VertexOperator.ncoeff (Y a) n) b = 0
  vacuum_mode_zero : ∀ v : V, (VertexOperator.ncoeff (Y vacuum) 0) v = v
  creation_mode_zero : ∀ v : V, (VertexOperator.ncoeff (Y v) 0) vacuum = v
  translation_vacuum : T vacuum = 0

attribute [instance] VOAData.instAddCommGroup VOAData.instModule

namespace VOAData

variable (A : VOAData)

/-- The normalized zero mode (`A[[0]]`) acting on states. -/
def zeroMode (a : A.V) : Module.End ℂ A.V :=
  VertexOperator.ncoeff (A.Y a) 0

@[simp] lemma zeroMode_apply (a : A.V) (v : A.V) :
    A.zeroMode a v = (VertexOperator.ncoeff (A.Y a) 0) v := rfl

end VOAData

/-- Scalar multiplication as an endomorphism of `ℂ`. -/
def scalarMode (a : ℂ) : Module.End ℂ ℂ :=
  a • LinearMap.id

private def scalarCoeffModel (a : ℂ) (n : ℤ) : Module.End ℂ ℂ :=
  if n = (-1 : ℤ) then scalarMode a else 0

private lemma scalarCoeffModel_trunc (a : ℂ) :
    ∀ x : ℂ, ∃ N : ℤ, ∀ m : ℤ, m < N → scalarCoeffModel a m x = 0 := by
  intro x
  refine ⟨(-1 : ℤ), ?_⟩
  intro m hm
  have hmne : m ≠ (-1 : ℤ) := by
    intro h
    subst h
    exact (lt_irrefl (-1 : ℤ)) hm
  simp [scalarCoeffModel, hmne]

/-- Toy vertex operator: only the coefficient at exponent `-1` is nonzero. -/
def scalarField (a : ℂ) : VertexOperator ℂ ℂ :=
  VertexOperator.of_coeff (scalarCoeffModel a) (scalarCoeffModel_trunc a)

lemma scalarField_mode_zero (a : ℂ) :
    VertexOperator.ncoeff (scalarField a) 0 = scalarMode a := by
  simp [scalarField, scalarCoeffModel, VertexOperator.ncoeff_of_coeff]

lemma scalarField_mode_zero_apply (a x : ℂ) :
    (VertexOperator.ncoeff (scalarField a) 0) x = a * x := by
  rw [scalarField_mode_zero]
  simp [scalarMode]

lemma scalarField_mode_ne_zero (a : ℂ) {n : ℤ} (hn : n ≠ 0) :
    VertexOperator.ncoeff (scalarField a) n = 0 := by
  have hmode :
      VertexOperator.ncoeff (scalarField a) n = scalarCoeffModel a (-n - 1) := by
    simp [scalarField, VertexOperator.ncoeff_of_coeff]
  rw [hmode, scalarCoeffModel]
  have hne : (-n - 1 : ℤ) ≠ (-1 : ℤ) := by
    intro h
    have hn0 : n = 0 := by linarith
    exact hn hn0
  simp [hne]

lemma scalarField_mode_eq (a : ℂ) (n : ℤ) :
    VertexOperator.ncoeff (scalarField a) n = if n = 0 then scalarMode a else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [scalarField_mode_zero]
  · simp [hn, scalarField_mode_ne_zero (a := a) hn]

/-- A toy kernel-pure VOA on `ℂ` with product given by scalar multiplication. -/
def scalarVOA : VOAData where
  V := ℂ
  instAddCommGroup := inferInstance
  instModule := inferInstance
  Y := scalarField
  vacuum := 1
  T := 0
  lower_trunc := by
    intro a b
    refine ⟨0, ?_⟩
    intro n hn
    have hmode : VertexOperator.ncoeff (scalarField a) n = 0 :=
      scalarField_mode_ne_zero (a := a) (n := n) (ne_of_lt hn)
    simp [hmode]
  vacuum_mode_zero := by
    intro v
    simpa using scalarField_mode_zero_apply (a := (1 : ℂ)) (x := v)
  creation_mode_zero := by
    intro v
    simpa using scalarField_mode_zero_apply (a := v) (x := (1 : ℂ))
  translation_vacuum := by
    simp

end HeytingLean.Moonshine.VOA
