import HeytingLean.Moonshine.VOA.Grading

set_option autoImplicit false

noncomputable section

open scoped VertexOperator

namespace HeytingLean.Moonshine.VOA

universe u

/-- Minimal module interface for a VOA. -/
structure VOARep (A : VOAData) where
  W : Type u
  instAddCommGroup : AddCommGroup W
  instModule : Module ℂ W
  YW : A.V → VertexOperator ℂ W
  lower_trunc :
    ∀ a : A.V, ∀ w : W, ∃ N : ℤ, ∀ n : ℤ, n < N → (VertexOperator.ncoeff (YW a) n) w = 0
  vacuum_mode_zero : ∀ w : W, (VertexOperator.ncoeff (YW A.vacuum) 0) w = w

attribute [instance] VOARep.instAddCommGroup VOARep.instModule

/-- Every VOA acts on itself by its own fields (regular module). -/
def regularRep (A : VOAData) : VOARep A where
  W := A.V
  instAddCommGroup := A.instAddCommGroup
  instModule := A.instModule
  YW := A.Y
  lower_trunc := A.lower_trunc
  vacuum_mode_zero := A.vacuum_mode_zero

/-- The regular module for the scalar toy VOA. -/
def scalarRegularRep : VOARep scalarVOA :=
  regularRep scalarVOA

end HeytingLean.Moonshine.VOA
