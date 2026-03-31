import HeytingLean.Moonshine.VOA.Modules

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.VOA

example : PairwiseLocal scalarVOA :=
  scalarVOA_pairwiseLocal

example : ZeroModeAssociative scalarVOA :=
  scalarVOA_zeroModeAssociative

example : ZeroModeCommutative scalarVOA :=
  scalarVOA_zeroModeCommutative

example : WeightGrading scalarVOA :=
  scalarWeightGrading

example : VOARep scalarVOA :=
  scalarRegularRep

example (a : ℂ) : scalarVOA.zeroMode a (1 : ℂ) = a := by
  change (VertexOperator.ncoeff (scalarField a) 0) (1 : ℂ) = a
  simpa using scalarField_mode_zero_apply (a := a) (x := (1 : ℂ))

end HeytingLean.Moonshine.VOA
