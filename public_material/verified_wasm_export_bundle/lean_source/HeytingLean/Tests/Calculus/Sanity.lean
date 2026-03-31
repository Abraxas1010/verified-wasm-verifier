import HeytingLean.Calculus.CalculusLens
import HeytingLean.Calculus.RModalCalculus
import HeytingLean.Calculus.Leibniz

/-!
Compile-only sanity for the Calculus lens scaffolding.
-/

namespace HeytingLean
namespace Tests
namespace Calculus

open HeytingLean.Calculus

def _inst : CalculusNucleus (Set (ℝ → ℝ)) := Calculus.Instances.smoothClosureId

def _omegaProp (S : Set (ℝ → ℝ)) : Prop :=
  S ∈ _inst.Omega

def _rmodal : RModal (Set (ℝ → ℝ)) := Calculus.ofCalculusNucleus _inst

def _leib : LeibnizAxioms _rmodal := { psr := True, occam := True, fict := True }

-- Fixed-point set is inf-closed under this minimal nucleus
def _omega_inf_closed (S T : Set (ℝ → ℝ)) :
    S ⊓ T ∈ _inst.Omega := by
  have hS : S ∈ _inst.Omega := by change _inst.R S = S; rfl
  have hT : T ∈ _inst.Omega := by change _inst.R T = T; rfl
  simpa using
    Calculus.CalculusNucleus.omega_inf_closed (N := _inst) hS hT

end Calculus
end Tests
end HeytingLean
