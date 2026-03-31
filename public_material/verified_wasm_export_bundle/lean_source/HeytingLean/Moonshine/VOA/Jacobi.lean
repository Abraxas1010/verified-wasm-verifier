import HeytingLean.Moonshine.VOA.Locality

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.VOA

/--
A compact proxy for the Jacobi/associativity content at this stage:
associativity of the normalized zero mode product.
-/
def ZeroModeAssociative (A : VOAData) : Prop :=
  ∀ a b c : A.V,
    A.zeroMode a (A.zeroMode b c) = A.zeroMode (A.zeroMode a b) c

/-- A commutativity companion for the zero-mode product. -/
def ZeroModeCommutative (A : VOAData) : Prop :=
  ∀ a b c : A.V,
    A.zeroMode a (A.zeroMode b c) = A.zeroMode b (A.zeroMode a c)

theorem scalarVOA_zeroModeAssociative : ZeroModeAssociative scalarVOA := by
  intro a b c
  change (VertexOperator.ncoeff (scalarField a) 0) ((VertexOperator.ncoeff (scalarField b) 0) c) =
      (VertexOperator.ncoeff (scalarField ((VertexOperator.ncoeff (scalarField a) 0) b)) 0) c
  simp [scalarField_mode_zero_apply, mul_assoc]

theorem scalarVOA_zeroModeCommutative : ZeroModeCommutative scalarVOA := by
  intro a b c
  change (VertexOperator.ncoeff (scalarField a) 0) ((VertexOperator.ncoeff (scalarField b) 0) c) =
      (VertexOperator.ncoeff (scalarField b) 0) ((VertexOperator.ncoeff (scalarField a) 0) c)
  simp [scalarField_mode_zero_apply, mul_left_comm]

end HeytingLean.Moonshine.VOA
