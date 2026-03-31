import HeytingLean.LoF.Synthesis.GrandCorrespondence
import HeytingLean.LoF.Correspondence.NucleusCorrespondence
import HeytingLean.LoF.Combinators.Topos.ClosureVsTruncation
import HeytingLean.LoF.MRSystems.Site
import HeytingLean.LoF.MRSystems.StablePropositions

/-!
# GrandCorrespondenceFull — Phase F “grand correspondence” package (objective)

This file packages the strongest **Lean-verifiable** correspondences available in this repository
between the five spec items:

1. `Ω_J` — Grothendieck-closed sieves (stable truth values in the topos layer).
2. `Ω_R` — fixed points of a nucleus/closure operator (same mechanism, different presentations).
3. “(-1)-truncation of SKY path ∞-groupoid” — formalized here as: thin reachability homs in the
   preorder category `StepsCat` are the propositional truncation of labeled multiway paths `LSteps`.
4. Heyting algebra of stable propositions — realized as the Heyting algebra structures on closed
   sieves and on stable selector predicates.
5. (M,R) closure — selector closure `closeSelector`, its kernel quotient, and the induced logic.

Objectivity boundary:
* We do **not** claim that `Ω_J` itself is a HoTT (-1)-truncation (`Trunc _`).  In fact, closed
  sieves are generally **not** subsingleton (already for the dense topology), so such an
  equivalence cannot exist in general; we prove this explicitly.
* The “(-1)-truncation” slogan is made precise at the **path-space** level (`Trunc (LSteps t u)`),
  not at the closed-sieve level.
-/

namespace HeytingLean
namespace LoF
namespace Synthesis

open scoped Classical

open CategoryTheory

/-! ## A bundled “grand correspondence” diagram -/

structure GrandCorrespondence where
  /- ### Topos layer: kernel quotient and nucleus fixed points -/

  topos_closeQuotEquivClosed :
      ∀ {C : Type} [Category C] (J : GrothendieckTopology C) (X : C),
        HeytingLean.LoF.Combinators.Topos.CloseQuot (J := J) X ≃
          HeytingLean.LoF.Combinators.Topos.ClosedSieve (C := C) J X

  topos_closedEquivFixed :
      ∀ {C : Type} [Category C] (J : GrothendieckTopology C) (X : C),
        HeytingLean.LoF.Combinators.Topos.ClosedSieve (C := C) J X ≃
          HeytingLean.LoF.Correspondence.Grothendieck.FixedSieve (C := C) J X

  /- ### SKY layer: (-1)-truncation boundary for path spaces -/

  sky_truncLStepsEquivStepsHom :
      ∀ (t u : HeytingLean.LoF.Combinators.Topos.StepsCat),
        Trunc (HeytingLean.LoF.Combinators.Category.LSteps t u) ≃ (t ⟶ u)

  /- ### (M,R) layer: kernel quotient, fixed points, and site-level closed sieves -/

  mr_closeQuotEquivClosedSelector :
      ∀ {S : HeytingLean.ClosingTheLoop.MR.MRSystem} {b : S.B}
        (RI : HeytingLean.ClosingTheLoop.MR.RightInverseAt S b),
        HeytingLean.LoF.MRSystems.CloseQuot (S := S) (b := b) RI ≃
          HeytingLean.LoF.MRSystems.ClosedSelector (S := S) (b := b) RI

  mr_closedSelectorEquivFixed :
      ∀ {S : HeytingLean.ClosingTheLoop.MR.MRSystem} {b : S.B}
        (RI : HeytingLean.ClosingTheLoop.MR.RightInverseAt S b),
        HeytingLean.LoF.MRSystems.ClosedSelector (S := S) (b := b) RI ≃
          HeytingLean.LoF.MRSystems.ClosedSelectorFixed (S := S) (b := b) RI

  mr_stablePropEquivHubClosedSieve :
      ∀ {S : HeytingLean.ClosingTheLoop.MR.MRSystem} {b : S.B}
        (RI : HeytingLean.ClosingTheLoop.MR.RightInverseAt S b),
        HeytingLean.LoF.MRSystems.StableProp (S := S) (b := b) RI ≃
          HeytingLean.LoF.MRSystems.SelectorSite.HubClosedSieve (S := S) (b := b) RI

  /- ### Counterexample: `Ω_J` is not a `Trunc` in general -/

  dense_noEquiv_closedSieve_trunc :
      ∀ {C : Type} [Category C] (X : C) (α : Type),
        ¬ Nonempty
            (HeytingLean.LoF.Combinators.Topos.ClosedSieve (C := C) (GrothendieckTopology.dense) X ≃
              Trunc α)

namespace GrandCorrespondence

open HeytingLean.LoF.Combinators
open HeytingLean.LoF.Combinators.Topos
open HeytingLean.LoF.MRSystems
open HeytingLean.ClosingTheLoop.MR

noncomputable def canonical : GrandCorrespondence := by
  classical
  refine
    { topos_closeQuotEquivClosed := ?_
      topos_closedEquivFixed := ?_
      sky_truncLStepsEquivStepsHom := ?_
      mr_closeQuotEquivClosedSelector := ?_
      mr_closedSelectorEquivFixed := ?_
      mr_stablePropEquivHubClosedSieve := ?_
      dense_noEquiv_closedSieve_trunc := ?_ }
  · intro C _ J X
    exact HeytingLean.LoF.Combinators.Topos.closeQuotEquivClosed (C := C) (J := J) X
  · intro C _ J X
    exact HeytingLean.LoF.Correspondence.Grothendieck.closedSieveEquivFixedSieve (C := C) (J := J) X
  · intro t u
    exact HeytingLean.LoF.Combinators.Topos.TruncationBoundary.truncLStepsEquivStepsHom t u
  · intro S b RI
    exact HeytingLean.LoF.MRSystems.closeQuotEquivClosed (S := S) (b := b) RI
  · intro S b RI
    exact HeytingLean.LoF.MRSystems.closedRangeEquivFixed (S := S) (b := b) RI
  · intro S b RI
    -- Stable propositions are just sets/predicates on closed selectors.
    -- `ΩClosed` is the sublocale of predicates containing the non-closed core, and it is equivalent
    -- to closed hub sieves in the selector-site topology.
    have eStable : StableProp (S := S) (b := b) RI ≃ ΩClosed (S := S) (b := b) RI := by
      -- `StableProp` is definitionaly `Set (ClosedSelectorFixed ...)`.
      simpa [StableProp, ClosedSelectorFixed'] using
        (ΩClosed.equivClosedSubsets (S := S) (b := b) RI).symm
    exact eStable.trans (SelectorSite.equivΩClosedHubClosedSieve (S := S) (b := b) RI)
  · intro C _ X α hEqv
    rcases hEqv with ⟨e⟩
    haveI : Subsingleton (ClosedSieve (C := C) (GrothendieckTopology.dense) X) :=
      (Equiv.subsingleton_congr e).2 (by infer_instance)
    exact DenseTopology.not_subsingleton_closedSieve_dense (C := C) X (by infer_instance)

end GrandCorrespondence

end Synthesis
end LoF
end HeytingLean
