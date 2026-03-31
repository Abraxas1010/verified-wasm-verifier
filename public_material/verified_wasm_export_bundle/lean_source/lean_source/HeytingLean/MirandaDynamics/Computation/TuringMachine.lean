/-!
# MirandaDynamics.Computation: deterministic and reversible machines (Lean spine)

This file provides a **non-axiomatic** interface layer for the “reversible computation” aspects
used in the Miranda billiards paper:

* a deterministic transition system on configurations,
* `stepN` iteration and a “halts-from” predicate,
* a simple notion of reversibility (`step` is injective),
* a Bennett-style *interface* that packages a reversible simulator **when provided**.

We do **not** claim Bennett’s existence theorem here; formalizing that existence proof is a large
separate project.  This module is the maximal honest mechanization: everything is defined and all
lemmas are proved, but “Bennett exists for all machines” is not asserted.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Computation

universe u v

/-- A deterministic step function on configurations. -/
structure DetSys (Cfg : Type u) where
  step : Cfg → Cfg

namespace DetSys

variable {Cfg : Type u}

/-- Iterate `step` for `n` steps. -/
def stepN (M : DetSys Cfg) : Nat → Cfg → Cfg
  | 0, c => c
  | Nat.succ n, c => stepN M n (M.step c)

@[simp] theorem stepN_zero (M : DetSys Cfg) (c : Cfg) : stepN M 0 c = c := by
  rfl

@[simp] theorem stepN_succ (M : DetSys Cfg) (n : Nat) (c : Cfg) :
    stepN M (n + 1) c = stepN M n (M.step c) := by
  cases n <;> rfl

/-- A deterministic system is reversible iff its step function is injective. -/
def IsReversible (M : DetSys Cfg) : Prop :=
  Function.Injective M.step

end DetSys

/-- A deterministic system equipped with a halting predicate. -/
structure HaltSys (Cfg : Type u) extends DetSys Cfg where
  halts : Cfg → Prop

namespace HaltSys

variable {Cfg : Type u}

abbrev stepN (M : HaltSys Cfg) (n : Nat) (c : Cfg) : Cfg :=
  DetSys.stepN M.toDetSys n c

@[simp] theorem stepN_zero (M : HaltSys Cfg) (c : Cfg) : M.stepN 0 c = c := by
  rfl

@[simp] theorem stepN_succ (M : HaltSys Cfg) (n : Nat) (c : Cfg) :
    M.stepN (n + 1) c = M.stepN n (M.step c) := by
  cases n <;> rfl

/-- `haltsAt M c n` means: after `n` steps from `c`, we are in a halting configuration. -/
def haltsAt (M : HaltSys Cfg) (c : Cfg) (n : Nat) : Prop :=
  M.halts (M.stepN n c)

/-- `haltsFrom M c` means: there exists a step count after which we halt. -/
def haltsFrom (M : HaltSys Cfg) (c : Cfg) : Prop :=
  ∃ n : Nat, M.haltsAt c n

end HaltSys

/-!
## Bennett-style interface (data only)

The following structure is the minimal contract needed downstream:

* a reversible simulator system `R` with injective step,
* an embedding/projection between original and simulator configurations,
* one-step simulation (`project (R.step (embed c)) = M.step c`),
* halting reflection along the embedding.

This is *not* an existence theorem: it can be instantiated by any concrete construction.
-/

structure BennettConstruction {Cfg : Type u} (M : HaltSys Cfg) where
  RevCfg : Type v
  R : HaltSys RevCfg
  reversible : DetSys.IsReversible R.toDetSys
  embed : Cfg → RevCfg
  project : RevCfg → Cfg
  project_embed : ∀ c, project (embed c) = c
  step_comm : ∀ c, project (R.step (embed c)) = M.step c
  halts_comm : ∀ c, M.halts c ↔ R.halts (embed c)

class HasBennettConstruction {Cfg : Type u} (M : HaltSys Cfg) where
  construction : BennettConstruction M

end Computation
end MirandaDynamics
end HeytingLean
