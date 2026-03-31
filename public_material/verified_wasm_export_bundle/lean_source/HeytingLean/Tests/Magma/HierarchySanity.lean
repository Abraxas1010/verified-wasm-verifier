import HeytingLean.Magma.PredecessorMap

namespace HeytingLean.Tests.Magma

open HeytingLean.Magma

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A]

#check pr_injective
#check pr_order_embedding
#check MagmaticUniverse.hierarchy_cumulative
#check MagmaticUniverse.strict_predecessor_drops_level

end HeytingLean.Tests.Magma
