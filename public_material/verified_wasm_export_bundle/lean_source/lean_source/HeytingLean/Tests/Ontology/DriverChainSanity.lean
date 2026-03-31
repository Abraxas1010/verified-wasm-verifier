import HeytingLean.Ontology.DriverChain

namespace HeytingLean.Tests.Ontology

open HeytingLean.Ontology
open HeytingLean.Representations.Radial

#check reentry_driverWitness
#check reentry_driverWitness_sheafGlue
#check reentry_driverWitness_ratchetTrajectory

section

variable {α : Type u} [HeytingLean.LoF.PrimaryAlgebra α]
variable (R : HeytingLean.LoF.Reentry α)
variable {G : RadialGraph}
variable (js : JRatchet.JState G)

example : DriverWitness (R := R) (js := js) :=
  reentry_driverWitness (R := R) (js := js)

end

end HeytingLean.Tests.Ontology

