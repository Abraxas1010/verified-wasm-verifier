import HeytingLean.Crypto.ConstructiveHardness.TaskSpec
import HeytingLean.Constructor.CT.InformationSound

/-!
# CT Security Theorem: No-cloning implies eavesdropping detectable

This is an interface-first CT-native security statement:
if an eavesdropping strategy would require cloning a superinformation medium, and cloning is
CT-impossible, then the strategy’s intercept task is CT-impossible.

This is the core “no-cloning ⇒ security” pattern that QKD instantiations should refine later.
-/

namespace HeytingLean
namespace Crypto
namespace ConstructiveHardness

open HeytingLean.Constructor.CT

universe u

/-- An eavesdropping strategy for a task model `CT`. -/
structure EavesdroppingStrategy (σ : Type u) (CT : TaskCT σ) where
  /-- The eavesdropping task (intercept and copy). -/
  intercept : HeytingLean.Constructor.CT.Task σ
  /-- Eve gains some information (specification-level statement). -/
  gains_info : Prop
  /-- Soundness: if `intercept` is possible, then the stated gain holds. -/
  sound : CT.possible intercept → gains_info

/-- A superinformation medium is secure against eavesdropping when any strategy whose success
would imply the ability to clone the medium is itself impossible. -/
def SecureAgainstEavesdropping (σ : Type u) (CT : TaskCT σ)
    (M : TaskCT.SuperinformationMedium σ CT) : Prop :=
  ∀ (E : EavesdroppingStrategy σ CT),
    (CT.possible E.intercept → CT.possible M.copyXY) →
      CT.impossible E.intercept

/-- Main security theorem: superinformation media are secure against any eavesdropping strategy
that would entail a cloning capability. -/
theorem superinfo_secure_against_eavesdropping
    {σ : Type u} (CT : TaskCT σ) (M : TaskCT.SuperinformationMedium σ CT) :
    SecureAgainstEavesdropping σ CT M := by
  intro E hRequiresCloning hPossible
  have hCopyPossible : CT.possible M.copyXY := hRequiresCloning hPossible
  exact M.no_copyXY hCopyPossible

end ConstructiveHardness
end Crypto
end HeytingLean

