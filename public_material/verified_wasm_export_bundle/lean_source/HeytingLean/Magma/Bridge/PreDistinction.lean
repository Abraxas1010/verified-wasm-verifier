import HeytingLean.Magma.Bridge.NucleusProjection
import HeytingLean.LoF.PrimaryAlgebra
import HeytingLean.LoF.MRSystems.Nucleus
import HeytingLean.Noneism.Core.Nucleus

namespace HeytingLean.Magma.Bridge

open HeytingLean.Magma
open HeytingLean

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A]

/-- The pre-distinction domain is witnessed by the existence of incomparable atoms. -/
def first_distinction : Prop :=
  ∃ a₀ a₁ : A, Incomparable a₀ a₁

omit u in
theorem first_distinction_exists : first_distinction (A := A) :=
  incomparable_pair_exists A

theorem pr_as_reentry (x : Magma A) :
    familyOf x = { y | y ≤ x } := by
  rfl

/-- Noneist nucleus-facing work already packages a fixed-point carrier `Ω`; the magmatic
remainder is the complementary pre-distinction domain before that stabilization. -/
abbrev noneist_fixed_core := HeytingLean.Noneism.Core.Omega

/-- Rosen-style `(M,R)` closure similarly produces a nucleus-fixed carrier of internally
closed selectors, matching the “resolved core carved from a larger ambient domain” pattern. -/
abbrev mr_closed_selector_core
    {S : HeytingLean.ClosingTheLoop.MR.MRSystem.{u_1, u_2}} {b : S.B}
    (RI : HeytingLean.ClosingTheLoop.MR.RightInverseAt S b) :=
  HeytingLean.LoF.MRSystems.ΩClosed (S := S) (b := b) RI

end HeytingLean.Magma.Bridge
