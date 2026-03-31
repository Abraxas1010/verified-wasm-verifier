/-
# PhysLean (Stable Import Set)

This module imports the PhysLean library (https://physlean.com) into the HeytingLean
environment, while excluding PhysLean modules that are known to fail (or depend on modules
known to fail) under our pinned toolchain.

Why this exists:
- HeytingLean depends on PhysLean, but the pinned backport (`Abraxas1010/PhysLean` @ `backport-v4.24.0`)
  currently has a small set of modules that do not build under Mathlib/Lean `v4.24.0`.
- Our local search/index tooling (`scripts/build_index.sh`) needs an importable module so it can
  enumerate `PhysLean.*` declarations for discoverability via `scripts/search.sh`.

Excluded roots (known failing modules):
- PhysLean.CondensedMatter.TightBindingChain.Basic
- PhysLean.Mathematics.Geometry.Metric.Riemannian.Defs
- PhysLean.Mathematics.InnerProductSpace.Basic
- PhysLean.Particles.StandardModel.HiggsBoson.Basic
- PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.OfPotentialTerm
- PhysLean.QFT.PerturbationTheory.FieldOpFreeAlgebra.SuperCommute
- PhysLean.QFT.PerturbationTheory.FieldSpecification.NormalOrder
- PhysLean.QFT.PerturbationTheory.WickContraction.UncontractedList
- PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.Completeness
- PhysLean.QuantumMechanics.OneDimension.Operators.Momentum
- PhysLean.SpaceAndTime.Space.Basic
- PhysLean.SpaceAndTime.Space.IsDistBounded

Import policy: keep 215 PhysLean root imports and exclude 177 that depend (transitively)
on the failing roots above.

Note: We intentionally omit a couple of PhysLean meta modules whose names contain tokens that
are forbidden in HeytingLean's repo-local "no proof escapes" guard. Those modules may still be
pulled transitively from inside `.lake/packages/PhysLean`; we just avoid importing them directly
from this wrapper (which lives under `lean/` and is scanned by the guard).

Regeneration: this file is generated from the upstream `PhysLean.lean` import list plus a failure blocklist.
-/

import PhysLean.ClassicalMechanics.Basic
import PhysLean.ClassicalMechanics.Pendulum.CoplanarDoublePendulum
import PhysLean.ClassicalMechanics.Pendulum.MiscellaneousPendulumPivotMotions
import PhysLean.ClassicalMechanics.Pendulum.SlidingPendulum
import PhysLean.ClassicalMechanics.Scattering.RigidSphere
import PhysLean.ClassicalMechanics.Vibrations.LinearTriatomic
import PhysLean.CondensedMatter.Basic
import PhysLean.Cosmology.Basic
import PhysLean.Electromagnetism.Charge.ChargeUnit
import PhysLean.Mathematics.DataStructures.FourTree.Basic
import PhysLean.Mathematics.DataStructures.FourTree.UniqueMap
import PhysLean.Mathematics.DataStructures.Matrix.LieTrace
import PhysLean.Mathematics.Distribution.Basic
import PhysLean.Mathematics.Distribution.PowMul
import PhysLean.Mathematics.FDerivCurry
import PhysLean.Mathematics.Fin
import PhysLean.Mathematics.Fin.Involutions
import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Defs
import PhysLean.Mathematics.LinearMaps
import PhysLean.Mathematics.List
import PhysLean.Mathematics.List.InsertIdx
import PhysLean.Mathematics.List.InsertionSort
import PhysLean.Mathematics.PiTensorProduct
import PhysLean.Mathematics.RatComplexNum
import PhysLean.Mathematics.SO3.Basic
import PhysLean.Mathematics.SchurTriangulation
import PhysLean.Mathematics.SpecialFunctions.PhysHermite
import PhysLean.Mathematics.Trigonometry.Tanh
import PhysLean.Meta.AllFilePaths
import PhysLean.Meta.Basic
import PhysLean.Meta.Informal.Basic
import PhysLean.Meta.Informal.Post
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.Meta.Notes.Basic
import PhysLean.Meta.Notes.HTMLNote
import PhysLean.Meta.Notes.NoteFile
import PhysLean.Meta.Notes.ToHTML
import PhysLean.Meta.Remark.Basic
import PhysLean.Meta.Remark.Properties
import PhysLean.Meta.TODO.Basic
import PhysLean.Meta.TransverseTactics
import PhysLean.Optics.Basic
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Basic
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.FamilyMaps
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.NoGrav.Basic
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Ordinary.Basic
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Ordinary.DimSevenPlane
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Ordinary.FamilyMaps
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Permutations
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.BMinusL
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.Basic
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.BoundPlaneDim
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.FamilyMaps
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.HyperCharge
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.PlaneNonSols
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.QuadSol
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.QuadSolToSol
import PhysLean.Particles.FlavorPhysics.CKMMatrix.Basic
import PhysLean.Particles.FlavorPhysics.CKMMatrix.Invariants
import PhysLean.Particles.FlavorPhysics.CKMMatrix.PhaseFreedom
import PhysLean.Particles.FlavorPhysics.CKMMatrix.Relations
import PhysLean.Particles.FlavorPhysics.CKMMatrix.Rows
import PhysLean.Particles.FlavorPhysics.CKMMatrix.StandardParameterization.Basic
import PhysLean.Particles.FlavorPhysics.CKMMatrix.StandardParameterization.StandardParameters
import PhysLean.Particles.NeutrinoPhysics.Basic
import PhysLean.Particles.StandardModel.AnomalyCancellation.Basic
import PhysLean.Particles.StandardModel.AnomalyCancellation.FamilyMaps
import PhysLean.Particles.StandardModel.AnomalyCancellation.NoGrav.Basic
import PhysLean.Particles.StandardModel.AnomalyCancellation.NoGrav.One.Lemmas
import PhysLean.Particles.StandardModel.AnomalyCancellation.NoGrav.One.LinearParameterization
import PhysLean.Particles.StandardModel.AnomalyCancellation.Permutations
import PhysLean.Particles.StandardModel.Representations
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.B3
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.Basic
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.HyperCharge
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.LineY3B3
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.OrthogY3B3.Basic
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.OrthogY3B3.PlaneWithY3B3
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.OrthogY3B3.ToSols
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.Permutations
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.Y3
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.Basic
import PhysLean.Particles.SuperSymmetry.SU5.ChargeSpectrum.OfFieldLabel
import PhysLean.Particles.SuperSymmetry.SU5.FieldLabels
import PhysLean.Particles.SuperSymmetry.SU5.Potential
import PhysLean.QFT.AnomalyCancellation.Basic
import PhysLean.QFT.AnomalyCancellation.GroupActions
import PhysLean.QFT.PerturbationTheory.CreateAnnihilate
import PhysLean.QFT.PerturbationTheory.FeynmanDiagrams.Basic
import PhysLean.QFT.PerturbationTheory.FieldStatistics.Basic
import PhysLean.QFT.PerturbationTheory.FieldStatistics.ExchangeSign
import PhysLean.QFT.PerturbationTheory.FieldStatistics.OfFinset
import PhysLean.QFT.PerturbationTheory.Koszul.KoszulSign
import PhysLean.QFT.PerturbationTheory.Koszul.KoszulSignInsert
import PhysLean.QFT.QED.AnomalyCancellation.Basic
import PhysLean.QFT.QED.AnomalyCancellation.BasisLinear
import PhysLean.QFT.QED.AnomalyCancellation.ConstAbs
import PhysLean.QFT.QED.AnomalyCancellation.Even.BasisLinear
import PhysLean.QFT.QED.AnomalyCancellation.Even.LineInCubic
import PhysLean.QFT.QED.AnomalyCancellation.Even.Parameterization
import PhysLean.QFT.QED.AnomalyCancellation.LineInPlaneCond
import PhysLean.QFT.QED.AnomalyCancellation.LowDim.One
import PhysLean.QFT.QED.AnomalyCancellation.LowDim.Three
import PhysLean.QFT.QED.AnomalyCancellation.LowDim.Two
import PhysLean.QFT.QED.AnomalyCancellation.Odd.BasisLinear
import PhysLean.QFT.QED.AnomalyCancellation.Odd.LineInCubic
import PhysLean.QFT.QED.AnomalyCancellation.Odd.Parameterization
import PhysLean.QFT.QED.AnomalyCancellation.Permutations
import PhysLean.QFT.QED.AnomalyCancellation.Sorts
import PhysLean.QFT.QED.AnomalyCancellation.VectorLike
import PhysLean.QuantumMechanics.FiniteTarget.Basic
import PhysLean.QuantumMechanics.FiniteTarget.HilbertSpace
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.Basic
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.Gaussians
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.PlaneWaves
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.PositionStates
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.SchwartzSubmodule
import PhysLean.QuantumMechanics.OneDimension.Operators.Parity
import PhysLean.QuantumMechanics.OneDimension.Operators.Position
import PhysLean.QuantumMechanics.OneDimension.Operators.Unbounded
import PhysLean.QuantumMechanics.PlanckConstant
import PhysLean.Relativity.Bispinors.Basic
import PhysLean.Relativity.CliffordAlgebra
import PhysLean.Relativity.LorentzAlgebra.Basic
import PhysLean.Relativity.LorentzAlgebra.Basis
import PhysLean.Relativity.LorentzAlgebra.ExponentialMap
import PhysLean.Relativity.LorentzGroup.Basic
import PhysLean.Relativity.LorentzGroup.Boosts.Generalized
import PhysLean.Relativity.LorentzGroup.Orthochronous.Basic
import PhysLean.Relativity.LorentzGroup.Proper
import PhysLean.Relativity.LorentzGroup.Restricted.Basic
import PhysLean.Relativity.LorentzGroup.Restricted.FromBoostRotation
import PhysLean.Relativity.LorentzGroup.Rotations
import PhysLean.Relativity.LorentzGroup.ToVector
import PhysLean.Relativity.MinkowskiMatrix
import PhysLean.Relativity.PauliMatrices.AsTensor
import PhysLean.Relativity.PauliMatrices.Basic
import PhysLean.Relativity.PauliMatrices.CliffordAlgebra
import PhysLean.Relativity.PauliMatrices.Relations
import PhysLean.Relativity.PauliMatrices.SelfAdjoint
import PhysLean.Relativity.PauliMatrices.ToTensor
import PhysLean.Relativity.SL2C.Basic
import PhysLean.Relativity.SL2C.SelfAdjoint
import PhysLean.Relativity.SpeedOfLight
import PhysLean.Relativity.Tensors.Basic
import PhysLean.Relativity.Tensors.Color.Basic
import PhysLean.Relativity.Tensors.Color.Discrete
import PhysLean.Relativity.Tensors.Color.Lift
import PhysLean.Relativity.Tensors.ComplexTensor.Basic
import PhysLean.Relativity.Tensors.ComplexTensor.Lemmas
import PhysLean.Relativity.Tensors.ComplexTensor.Matrix.Pre
import PhysLean.Relativity.Tensors.ComplexTensor.Metrics.Basic
import PhysLean.Relativity.Tensors.ComplexTensor.Metrics.Lemmas
import PhysLean.Relativity.Tensors.ComplexTensor.Metrics.Pre
import PhysLean.Relativity.Tensors.ComplexTensor.OfRat
import PhysLean.Relativity.Tensors.ComplexTensor.Units.Basic
import PhysLean.Relativity.Tensors.ComplexTensor.Units.Pre
import PhysLean.Relativity.Tensors.ComplexTensor.Units.Symm
import PhysLean.Relativity.Tensors.ComplexTensor.Vector.Pre.Basic
import PhysLean.Relativity.Tensors.ComplexTensor.Vector.Pre.Contraction
import PhysLean.Relativity.Tensors.ComplexTensor.Vector.Pre.Modules
import PhysLean.Relativity.Tensors.ComplexTensor.Weyl.Basic
import PhysLean.Relativity.Tensors.ComplexTensor.Weyl.Contraction
import PhysLean.Relativity.Tensors.ComplexTensor.Weyl.Metric
import PhysLean.Relativity.Tensors.ComplexTensor.Weyl.Modules
import PhysLean.Relativity.Tensors.ComplexTensor.Weyl.Two
import PhysLean.Relativity.Tensors.ComplexTensor.Weyl.Unit
import PhysLean.Relativity.Tensors.Constructors
import PhysLean.Relativity.Tensors.Contraction.Basic
import PhysLean.Relativity.Tensors.Contraction.Basis
import PhysLean.Relativity.Tensors.Contraction.Products
import PhysLean.Relativity.Tensors.Contraction.Pure
import PhysLean.Relativity.Tensors.Dual
import PhysLean.Relativity.Tensors.Elab
import PhysLean.Relativity.Tensors.Evaluation
import PhysLean.Relativity.Tensors.MetricTensor
import PhysLean.Relativity.Tensors.OfInt
import PhysLean.Relativity.Tensors.Product
import PhysLean.Relativity.Tensors.RealTensor.Basic
import PhysLean.Relativity.Tensors.RealTensor.CoVector.Basic
import PhysLean.Relativity.Tensors.RealTensor.Derivative
import PhysLean.Relativity.Tensors.RealTensor.Matrix.Pre
import PhysLean.Relativity.Tensors.RealTensor.Metrics.Basic
import PhysLean.Relativity.Tensors.RealTensor.Metrics.Pre
import PhysLean.Relativity.Tensors.RealTensor.ToComplex
import PhysLean.Relativity.Tensors.RealTensor.Units.Pre
import PhysLean.Relativity.Tensors.RealTensor.Vector.Basic
import PhysLean.Relativity.Tensors.RealTensor.Vector.Causality.Basic
import PhysLean.Relativity.Tensors.RealTensor.Vector.Causality.LightLike
import PhysLean.Relativity.Tensors.RealTensor.Vector.Causality.TimeLike
import PhysLean.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct
import PhysLean.Relativity.Tensors.RealTensor.Vector.Pre.Basic
import PhysLean.Relativity.Tensors.RealTensor.Vector.Pre.Contraction
import PhysLean.Relativity.Tensors.RealTensor.Vector.Pre.Modules
import PhysLean.Relativity.Tensors.RealTensor.Velocity.Basic
import PhysLean.Relativity.Tensors.TensorSpecies.Basic
import PhysLean.Relativity.Tensors.Tensorial
import PhysLean.Relativity.Tensors.UnitTensor
import PhysLean.SpaceAndTime.Time.TimeMan
import PhysLean.StatisticalMechanics.BoltzmannConstant
import PhysLean.StatisticalMechanics.CanonicalEnsemble.Basic
import PhysLean.StatisticalMechanics.CanonicalEnsemble.Finite
import PhysLean.StatisticalMechanics.CanonicalEnsemble.Lemmas
import PhysLean.StatisticalMechanics.CanonicalEnsemble.TwoState
import PhysLean.StringTheory.Basic
import PhysLean.StringTheory.FTheory.SU5.Basic
import PhysLean.StringTheory.FTheory.SU5.Charges.OfRationalSection
import PhysLean.StringTheory.FTheory.SU5.Fluxes.Basic
import PhysLean.StringTheory.FTheory.SU5.Fluxes.NoExotics.ChiralIndices
import PhysLean.StringTheory.FTheory.SU5.Fluxes.NoExotics.Completeness
import PhysLean.StringTheory.FTheory.SU5.Fluxes.NoExotics.Elems
import PhysLean.Thermodynamics.Basic
import PhysLean.Thermodynamics.IdealGas.Basic
import PhysLean.Thermodynamics.Temperature.Basic
import PhysLean.Units.Dimension
