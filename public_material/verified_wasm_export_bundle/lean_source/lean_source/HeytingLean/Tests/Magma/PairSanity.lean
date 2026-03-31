import HeytingLean.Magma.OrderedPair

namespace HeytingLean.Tests.Magma

open HeytingLean.Magma

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A] [PairEncoding A]

#check pair_injective
#check collateral_subpairs

end HeytingLean.Tests.Magma
