import HeytingLean.Magma.Separation.ReplacementFailure

namespace HeytingLean.Tests.Magma

open HeytingLean.Magma
open HeytingLean.Magma.Separation

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A] [PairEncoding A] [ProductEncoding A]
  [SeparationPresentation A]

#check magmatic_separation_scheme
#check predecessorImage
#check ReplacementCounterexample
#check replacement_fails

end HeytingLean.Tests.Magma
