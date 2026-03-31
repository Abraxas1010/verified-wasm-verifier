import HeytingLean.Ontology.PrimordialSheafBridge

namespace HeytingLean.Tests.Ontology

open HeytingLean.Ontology
open HeytingLean.PerspectivalPlenum.LensSheaf

#check eulerPhaseLaw_singleton_glues
#check eulerPhaseLaw_pair_glues_of_eq
#check reentry_supported_singleton_glues
#check reentry_supported_existsInPlenum
#check reentry_nucleus_euler_sheaf_glue

section

variable {α : Type u} [HeytingLean.LoF.PrimaryAlgebra α]
variable (R : HeytingLean.LoF.Reentry α)

example :
    ExistsInPlenum ((supported_oscillation (R := R)).enhances) :=
  reentry_supported_existsInPlenum (R := R)

end

end HeytingLean.Tests.Ontology

