import HeytingLean.ClosingTheLoop.MR.ClosureOperator
import HeytingLean.ClosingTheLoop.MR.YonedaBridge
import HeytingLean.Genesis.EigenformSoup.Bridge
import HeytingLean.Ontology.Primordial
import HeytingLean.Representations.Radial.JRatchet
import HeytingLean.Topos.JRatchet

namespace HeytingLean
namespace Ontology
namespace SelectorLoopPairwiseBridge

open ClosingTheLoop.MR
open Representations.Radial
open Topos.JRatchet

universe u v

/--
Typed bridge contract from selector-loop closure (`closeSelector` fixed points)
to the eigenform witness family.
-/
structure SelectorToEigenformBridge
    (Sys : MRSystem.{u, v}) (b : Sys.B) (RI : RightInverseAt Sys b)
    (nuc : HeytingLean.Genesis.EigenformSoup.SoupNucleus) where
  toSupport : Selector Sys → HeytingLean.Genesis.EigenformSoup.Support
  closed_to_eigenform :
    ∀ Φ : Selector Sys,
      IsClosed Sys b RI Φ →
      HeytingLean.Genesis.EigenformSoup.isEigenform nuc (toSupport Φ)

/--
Sheaf-glue hook: if a selector-loop closed state maps to an eigenform witness,
we get the corresponding re-entry fixed-point theorem.
-/
theorem pairwise_glue_selector_loop_to_eigenform_hook
    {Sys : MRSystem.{u, v}} {b : Sys.B} (RI : RightInverseAt Sys b)
    {nuc : HeytingLean.Genesis.EigenformSoup.SoupNucleus}
    (B : SelectorToEigenformBridge Sys b RI nuc)
    (bridge : HeytingLean.Genesis.EigenformSoup.ReentryBridgeWitness nuc)
    (Φ : Selector Sys) :
    IsClosed Sys b RI Φ →
    bridge.reentry.nucleus (B.toSupport Φ) = B.toSupport Φ := by
  intro hClosed
  exact HeytingLean.Genesis.EigenformSoup.eigenform_to_reentry_fixed bridge
    (B.closed_to_eigenform Φ hClosed)

/--
Typed bridge contract from selector-loop closure to the Euler-phase witness family.
-/
structure SelectorToEulerBridge
    (Sys : MRSystem.{u, v}) (b : Sys.B) (RI : RightInverseAt Sys b)
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) where
  closed_to_euler :
    ∀ Φ : Selector Sys,
      IsClosed Sys b RI Φ →
      EulerPhaseLaw ((supported_oscillation (R := R)).enhances)

/--
Sheaf-glue hook: selector-loop closed states can be projected to Euler-phase witnesses.
-/
theorem pairwise_glue_selector_loop_to_euler_hook
    {Sys : MRSystem.{u, v}} {b : Sys.B} (RI : RightInverseAt Sys b)
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α)
    (B : SelectorToEulerBridge Sys b RI (R := R))
    (Φ : Selector Sys) :
    IsClosed Sys b RI Φ →
    EulerPhaseLaw ((supported_oscillation (R := R)).enhances) := by
  intro hClosed
  exact B.closed_to_euler Φ hClosed

/--
Typed bridge contract from selector-loop closure to J-ratchet trajectories.
-/
structure SelectorToJRatchetBridge
    (Sys : MRSystem.{u, v}) (b : Sys.B) (RI : RightInverseAt Sys b)
    (G : RadialGraph) where
  toState : Selector Sys → JRatchet.JState G
  closed_to_trajectory :
    ∀ Φ : Selector Sys,
      IsClosed Sys b RI Φ →
      Topos.JRatchet.RatchetTrajectory (JRatchet.JState.spentFuel (toState Φ))

/--
Sheaf-glue hook: selector-loop closed states can be projected to J-ratchet trajectories.
-/
theorem pairwise_glue_selector_loop_to_jratchet_hook
    {Sys : MRSystem.{u, v}} {b : Sys.B} (RI : RightInverseAt Sys b)
    {G : RadialGraph}
    (B : SelectorToJRatchetBridge Sys b RI G)
    (Φ : Selector Sys) :
    IsClosed Sys b RI Φ →
    Topos.JRatchet.RatchetTrajectory (JRatchet.JState.spentFuel (B.toState Φ)) := by
  intro hClosed
  exact B.closed_to_trajectory Φ hClosed

theorem pairwise_glue_selector_loop_to_yoneda_idempotent_hook
    {Sys : MRSystem.{u, v}} {b : Sys.B} (RI : RightInverseAt Sys b)
    (Φ : Selector Sys) :
    HeytingLean.ClosingTheLoop.MR.selectorEndomorphism (S := Sys) (b := b) RI
      (HeytingLean.ClosingTheLoop.MR.selectorEndomorphism (S := Sys) (b := b) RI Φ) =
    HeytingLean.ClosingTheLoop.MR.selectorEndomorphism (S := Sys) (b := b) RI Φ := by
  simpa [HeytingLean.ClosingTheLoop.MR.selectorEndomorphism] using
    (HeytingLean.ClosingTheLoop.MR.closeSelector.idem (S := Sys) (b := b) (RI := RI) Φ)

/--
Typed bridge contract from eigenform witnesses to selector-loop closure.
-/
structure EigenformToSelectorLoopBridge
    (Sys : MRSystem.{u, v}) (b : Sys.B) (RI : RightInverseAt Sys b)
    (nuc : HeytingLean.Genesis.EigenformSoup.SoupNucleus) where
  fromSupport : HeytingLean.Genesis.EigenformSoup.Support → Selector Sys
  eigenform_to_closed :
    ∀ X : HeytingLean.Genesis.EigenformSoup.Support,
      HeytingLean.Genesis.EigenformSoup.isEigenform nuc X →
      IsClosed Sys b RI (fromSupport X)

/--
Reverse-direction hook: eigenform witnesses transport into selector-loop closure.
-/
theorem pairwise_glue_eigenform_to_selector_loop_hook
    {Sys : MRSystem.{u, v}} {b : Sys.B} (RI : RightInverseAt Sys b)
    {nuc : HeytingLean.Genesis.EigenformSoup.SoupNucleus}
    (B : EigenformToSelectorLoopBridge Sys b RI nuc)
    (X : HeytingLean.Genesis.EigenformSoup.Support) :
    HeytingLean.Genesis.EigenformSoup.isEigenform nuc X →
    IsClosed Sys b RI (B.fromSupport X) := by
  intro hEigen
  exact B.eigenform_to_closed X hEigen

/--
Typed bridge contract from Euler-phase witnesses to selector-loop closure.
-/
structure EulerToSelectorLoopBridge
    (Sys : MRSystem.{u, v}) (b : Sys.B) (RI : RightInverseAt Sys b)
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α) where
  fromEuler : Selector Sys
  euler_to_closed :
    EulerPhaseLaw ((supported_oscillation (R := R)).enhances) →
    IsClosed Sys b RI fromEuler

/--
Reverse-direction hook: Euler-phase witnesses transport into selector-loop closure.
-/
theorem pairwise_glue_euler_to_selector_loop_hook
    {Sys : MRSystem.{u, v}} {b : Sys.B} (RI : RightInverseAt Sys b)
    {α : Type u} [LoF.PrimaryAlgebra α] (R : LoF.Reentry α)
    (B : EulerToSelectorLoopBridge Sys b RI (R := R)) :
    EulerPhaseLaw ((supported_oscillation (R := R)).enhances) →
    IsClosed Sys b RI B.fromEuler := by
  intro hEuler
  exact B.euler_to_closed hEuler

/--
Typed bridge contract from J-ratchet trajectories to selector-loop closure.
-/
structure JRatchetToSelectorLoopBridge
    (Sys : MRSystem.{u, v}) (b : Sys.B) (RI : RightInverseAt Sys b)
    (G : RadialGraph) where
  fromTrajectory : JRatchet.JState G → Selector Sys
  jratchet_to_closed :
    ∀ js : JRatchet.JState G,
      Topos.JRatchet.RatchetTrajectory (JRatchet.JState.spentFuel js) →
      IsClosed Sys b RI (fromTrajectory js)

/--
Reverse-direction hook: J-ratchet trajectories transport into selector-loop closure.
-/
theorem pairwise_glue_jratchet_to_selector_loop_hook
    {Sys : MRSystem.{u, v}} {b : Sys.B} (RI : RightInverseAt Sys b)
    {G : RadialGraph}
    (js : JRatchet.JState G)
    (B : JRatchetToSelectorLoopBridge Sys b RI G) :
    Topos.JRatchet.RatchetTrajectory (JRatchet.JState.spentFuel js) →
    IsClosed Sys b RI (B.fromTrajectory js) := by
  intro hJ
  exact B.jratchet_to_closed js hJ

end SelectorLoopPairwiseBridge
end Ontology
end HeytingLean
