import HeytingLean.Crypto.ConstructiveHardness.ContextualityPhysical
import HeytingLean.Crypto.ConstructiveHardness.PhysicalModality
import HeytingLean.Constructor.CT.TaskExistence

/-!
# Task → Prop bridge (TaskSpec)

`HeytingLean.Crypto.ConstructiveHardness` currently provides a sound “physical possibility”
modality on propositions (`PhysicalModality`, `Φ P → P`) and a constructor-existence interface
directly on propositions (`PropCT`).

Separately, `HeytingLean.Constructor.CT.TaskExistence` provides constructor existence for CT tasks
(`TaskCT.possible`).

This file bridges the two layers by supplying a *specification* for tasks and extracting an
induced proposition-level `PhysicalModality`. It also provides a small lemma turning
`NoGlobalSection` into task-level impossibility under any sound task embedding.
-/

namespace HeytingLean
namespace Crypto
namespace ConstructiveHardness

open HeytingLean.Constructor.CT
open HeytingLean.LoF.CryptoSheaf.Quantum

universe u v

/-- A proposition-level specification for CT tasks over a fixed task model `CT`. -/
structure TaskSpec (σ : Type u) (CT : TaskCT σ) where
  /-- A predicate expressing that a task meets its intended spec. -/
  Spec : HeytingLean.Constructor.CT.Task σ → Prop
  /-- Soundness: if a task is possible (constructor exists), its spec holds. -/
  sound : ∀ T : HeytingLean.Constructor.CT.Task σ, CT.possible T → Spec T

namespace TaskSpec

variable {σ : Type u} {CT : TaskCT σ} (TS : TaskSpec σ CT)

/-- A `TaskSpec` induces a sound proposition-level physical modality:
`Φ P` means “there exists a possible task whose spec implies `P`”. -/
def toPhysicalModality : PhysicalModality where
  toFun P := ∃ T : HeytingLean.Constructor.CT.Task σ, CT.possible T ∧ (TS.Spec T → P)
  mono := by
    intro P Q hPQ
    rintro ⟨T, hT, hSpecP⟩
    refine ⟨T, hT, ?_⟩
    intro hSpec
    exact hPQ (hSpecP hSpec)
  sound := by
    intro P h
    rcases h with ⟨T, hT, hSpecP⟩
    exact hSpecP (TS.sound T hT)

end TaskSpec

/-!
## Contextuality ⇒ task-level impossibility (via a sound embedding)

If a task model provides a CT task that would *soundly* witness the existence of a global section,
then any `NoGlobalSection` obstruction makes that task CT-impossible.
-/

theorem contextuality_implies_task_impossible
    {σ : Type u} (CT : TaskCT σ)
    (X : Context) (cover : Finset Context)
    (e : EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X)
    (T : HeytingLean.Constructor.CT.Task σ)
    (T_sound : CT.possible T → GlobalSectionTask X cover e coverSubX) :
    NoGlobalSection X cover e coverSubX →
      CT.impossible T := by
  intro hNo hPossible
  have hNot :
      ¬ GlobalSectionTask X cover e coverSubX :=
    contextuality_implies_not_globalSectionTask
      (X := X) (cover := cover) (e := e) (coverSubX := coverSubX) hNo
  exact hNot (T_sound hPossible)

end ConstructiveHardness
end Crypto
end HeytingLean
