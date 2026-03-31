import HeytingLean.MirandaDynamics.Fluids.TuringComplete

/-!
# Tests: MirandaDynamics fluids sanity

These checks ensure the external-interface chain for the fluids lane is
available and that the undecidability theorems are exported with the expected
types.
-/

namespace HeytingLean.Tests.MirandaDynamics

open HeytingLean.MirandaDynamics

#check @Fluids.ContactFormData
#check @Fluids.BeltramiFieldData
#check @Fluids.CosymplecticData
#check @Fluids.HarmonicFieldData
#check @Fluids.CosymplecticReebIsHarmonic
#check @Fluids.EtnyreGhristCorrespondence
#check @Fluids.SharedOrbitWitness
#check @Fluids.NavierStokesSolution
#check @Fluids.HarmonicViscosityInvariance
#check @Fluids.CosymplecticEulerConstruction
#check @Fluids.FluidTuringConstruction
#check @Fluids.PeriodicityDetection

#check @Fluids.fluid_trajectory_undecidable
#check @Fluids.fluid_periodicity_undecidable
#check @Fluids.fluidPeriodicNucleus
#check @Fluids.fluidPeriodicNucleus_fixed_iff

end HeytingLean.Tests.MirandaDynamics
