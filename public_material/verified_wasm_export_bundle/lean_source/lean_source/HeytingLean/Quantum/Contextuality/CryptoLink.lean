import HeytingLean.Quantum.Contextuality.Triangle
import HeytingLean.Crypto.ConstructiveHardness.TaskPossible
import HeytingLean.Crypto.ConstructiveHardness.TaskSpec

/-!
# Contextuality → cryptographic “advantage” (impossibility link)

This module provides the Phase 9 “crypto link theorem” in a stable namespace:

*If an empirical model has no global section (contextuality witness), then under any sound notion of
physical “possibility” (constructors/tasks), the corresponding global-assignment task is impossible.*

We implement this as thin wrappers around the already-landed bridge lemmas in
`HeytingLean.Crypto.ConstructiveHardness.*`.
-/

namespace HeytingLean
namespace Quantum
namespace Contextuality
namespace CryptoLink

open HeytingLean.LoF.CryptoSheaf.Quantum
open HeytingLean.Crypto.ConstructiveHardness

universe u

/-- Contextuality rules out any constructor (sound PropCT) that would realize a global section. -/
theorem contextuality_implies_no_constructor
    (CT : PropCT)
    (X : Context) (cover : Finset Context)
    (e : EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) :
    NoGlobalSection X cover e coverSubX →
      CT.impossible (GlobalSectionTask X cover e coverSubX) := by
  intro hNo
  exact PropCT.contextuality_implies_no_constructor
    (CT := CT) (X := X) (cover := cover) (e := e) (coverSubX := coverSubX) hNo

/-- Triangle instance: any sound PropCT declares the global-section task impossible. -/
theorem triangle_no_constructor_globalSectionTask (CT : PropCT) :
    CT.impossible (GlobalSectionTask Triangle.X Triangle.cover Triangle.model Triangle.coverSubX) := by
  exact contextuality_implies_no_constructor
    (CT := CT) (X := Triangle.X) (cover := Triangle.cover) (e := Triangle.model)
    (coverSubX := Triangle.coverSubX) Triangle.noGlobal

/-- Task-level variant: any sound embedding of a CT task into the global-section task makes that task
impossible under contextuality. -/
theorem contextuality_implies_task_impossible
    {σ : Type u} (CT : HeytingLean.Constructor.CT.TaskCT σ)
    (X : Context) (cover : Finset Context)
    (e : EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X)
    (T : HeytingLean.Constructor.CT.Task σ)
    (T_sound : CT.possible T → GlobalSectionTask X cover e coverSubX) :
    NoGlobalSection X cover e coverSubX →
      CT.impossible T := by
  intro hNo
  exact HeytingLean.Crypto.ConstructiveHardness.contextuality_implies_task_impossible
    (CT := CT) (X := X) (cover := cover) (e := e) (coverSubX := coverSubX) (T := T)
    (T_sound := T_sound) hNo

end CryptoLink
end Contextuality
end Quantum
end HeytingLean
