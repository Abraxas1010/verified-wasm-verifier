import HeytingLean.Ontology.SheafGlueMatrix

namespace HeytingLean.Tests.Ontology

open HeytingLean.Ontology
open HeytingLean.Representations.Radial

#check matrix_edge_rnucleus_sheaf
#check matrix_edge_driver_sheaf
#check matrix_edge_jratchet_driver
#check matrix_projection_core
#check sheaf_glue_matrix_core

section

variable {α : Type u} [HeytingLean.LoF.PrimaryAlgebra α]
variable (R : HeytingLean.LoF.Reentry α)
variable {G : RadialGraph}
variable (js : JRatchet.JState G)

example : sheaf_glue_matrix_core (R := R) (js := js) := by
  simpa using (sheaf_glue_matrix_core (R := R) (js := js))

end

end HeytingLean.Tests.Ontology
