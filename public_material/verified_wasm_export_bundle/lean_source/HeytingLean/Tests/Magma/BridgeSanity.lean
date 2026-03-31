import HeytingLean.Magma.Bridge.ComputationalIrreducibility
import HeytingLean.Magma.Bridge.HeytingGapMeasure
import HeytingLean.Magma.Bridge.PreDistinction
import HeytingLean.Magma.Bridge.ScaleInvariance

namespace HeytingLean.Tests.Magma

open HeytingLean.Magma
open HeytingLean.Magma.Bridge
open HeytingLean.Magma.Separation

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A] [PairEncoding A] [ProductEncoding A]
  [SeparationPresentation A]

#check MagmaticNucleus.resolves_on_fixed
#check ResolvesCollateralAt
#check fixed_core_magmatic
#check scale_invariance_triple_equivalence
#check gap_zero_iff_fixed
#check irreducible_has_nonzero_gap
#check first_distinction_exists
#check pr_as_reentry
#check noneist_fixed_core
#check mr_closed_selector_core

end HeytingLean.Tests.Magma
