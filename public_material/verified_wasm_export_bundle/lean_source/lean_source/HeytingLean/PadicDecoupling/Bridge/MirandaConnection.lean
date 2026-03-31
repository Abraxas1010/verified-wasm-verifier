import HeytingLean.PadicDecoupling.Bridge.HossenfelderConnection
import HeytingLean.MirandaDynamics.Fluids.TuringComplete

noncomputable section

namespace HeytingLean.PadicDecoupling.Bridge

open HeytingLean.PadicDecoupling.Nucleus
open HeytingLean.MirandaDynamics

variable (p : ℕ) [Fact p.Prime]

theorem padic_fixed_iff_within_visible_skeleton (k : ℕ) (S : DepthState p) :
    S ∈ fixedPointsAtDepth p k ↔ asSet p S ⊆ roundedSkeleton p k :=
  mem_fixedPointsAtDepth_iff (p := p)

theorem miranda_fixed_iff_contains_periodic {α : Type*} (periodic : α → Prop) (S : Set α) :
    Fluids.fluidPeriodicNucleus periodic S = S ↔ {x | periodic x} ⊆ S :=
  Fluids.fluidPeriodicNucleus_fixed_iff periodic S

end HeytingLean.PadicDecoupling.Bridge
