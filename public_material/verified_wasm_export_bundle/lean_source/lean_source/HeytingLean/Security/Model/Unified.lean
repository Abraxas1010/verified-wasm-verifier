import HeytingLean.Security.Model.Computational
import HeytingLean.Security.Model.InformationTheoretic
import HeytingLean.Security.Model.Physical
import HeytingLean.Security.Composable.UC

namespace HeytingLean
namespace Security
namespace Model

/-!
# Unified security model (Phase 1 scaffold)

This module ties together the three security paradigms used by the unified crypto roadmap:
- computational (PQC),
- information-theoretic (QKD), and
- physical (Constructor Theory).

Universal Composability (UC) proper is scheduled for Phase 2; for Phase 1 we only provide a
*bridge interface* that later phases can instantiate.
-/

/-- Security paradigms tracked by the unified roadmap. -/
inductive Paradigm where
  | computational
  | informationTheoretic
  | physical

namespace Unified

open HeytingLean.Security.Composable

/-- Interface packaging a CT→UC bridge for a specific CT nucleus/task and an ideal/real pair. -/
class CTImpliesUC {σ : Type u} (J : HeytingLean.Constructor.CT.CTNucleus σ)
    (task : HeytingLean.Constructor.CT.Task σ)
    (F : IdealFunctionality) (π : Protocol F) : Prop where
  bridge : Physical.CTSecure (J := J) task → HeytingLean.Security.Composable.UCSecure F π

/-- Convenience lemma: if a CT→UC bridge instance is provided, CT-impossibility implies UC-security. -/
def ct_impossible_implies_uc_secure {σ : Type u}
    {J : HeytingLean.Constructor.CT.CTNucleus σ} {task : HeytingLean.Constructor.CT.Task σ}
    {F : IdealFunctionality} {π : Protocol F} [CTImpliesUC (J := J) (task := task) F π] :
    Physical.CTSecure (J := J) task → HeytingLean.Security.Composable.UCSecure F π :=
  CTImpliesUC.bridge (J := J) (task := task) (F := F) (π := π)

end Unified

end Model
end Security
end HeytingLean
