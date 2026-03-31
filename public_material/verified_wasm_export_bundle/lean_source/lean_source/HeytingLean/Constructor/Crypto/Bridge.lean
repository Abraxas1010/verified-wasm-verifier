import HeytingLean.Constructor.Crypto.NoCloning
import HeytingLean.Security.Composable.Composition

/-!
# CT → UC bridge (reduction-based, interface-first)

This file formalizes the standard reduction pattern used in the unified crypto roadmap:

- assume a protocol `π` for an ideal functionality `F`,
- assume a simulator `sim` and an indistinguishability predicate `Indistinguishable`,
- assume a *reduction* that turns any successful real/ideal distinguishing into CT-possibility of
  a designated “bad” task (often: cloning),
- then if that bad task is CT-impossible, conclude `UCSecure F π`.

This is intentionally not a global UC theorem: it is a local, assumption-packaged bridge.
-/

namespace HeytingLean
namespace Constructor
namespace Crypto

open HeytingLean.Security.Composable
open HeytingLean.Constructor.CT

universe u v w

variable {σ : Type u}

/-- A packaged reduction from UC distinguishing to CT-possibility of a designated “bad” task. -/
structure CTtoUCReduction
    (CT : TaskCT σ)
    (Tbad : BadTask σ)
    (F : IdealFunctionality.{u, v, w}) where
  π : Protocol F
  sim : Simulator F π
  Indistinguishable :
    (F.Input → F.Output × π.Message) → (F.Input → F.Output × π.Message) → Prop
  /-- If real and ideal are distinguishable, then the bad task is possible. -/
  reduction :
    ¬ Indistinguishable (realExecution (π := π)) (idealExecution (π := π) sim) →
      CT.possible Tbad.task

/-- Core bridge lemma: CT-impossibility of the bad task implies UC security (under a reduction). -/
theorem ct_to_uc_security
    {CT : TaskCT σ} {Tbad : BadTask σ} {F : IdealFunctionality.{u, v, w}}
    (R : CTtoUCReduction (CT := CT) (Tbad := Tbad) F)
    (hBad : CT.impossible Tbad.task) :
    UCSecure F R.π := by
  refine ⟨R.sim, R.Indistinguishable, ?_⟩
  by_contra h
  exact hBad (R.reduction h)

/-- Convenience specialization: when the “bad” task is a cloning task, a `NoCloning` premise
is enough to conclude UC security. -/
theorem noCloning_to_uc_security
    {CT : TaskCT σ} {Tclone : CloningTask σ} {F : IdealFunctionality.{u, v, w}}
    (R : CTtoUCReduction (CT := CT) (Tbad := ⟨Tclone.task⟩) F)
    (hNoClone : NoCloning CT Tclone) :
    UCSecure F R.π :=
  ct_to_uc_security (R := R) hNoClone

end Crypto
end Constructor
end HeytingLean

