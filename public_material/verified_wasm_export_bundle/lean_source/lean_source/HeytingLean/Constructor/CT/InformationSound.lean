import HeytingLean.Constructor.CT.TaskExistence

/-!
# CT information media (sound layer, constructor-existence)

`HeytingLean.Constructor.CT.Information` packages information variables for the nucleus-based CT layer.
This file provides a parallel, nucleus-free interface built on `TaskCT` (constructor existence).

It is intentionally interface-first: concrete physics (e.g. quantum no-cloning) will instantiate
these structures later.
-/

namespace HeytingLean
namespace Constructor
namespace CT

universe u v

variable {σ : Type u}

namespace TaskCT

variable (CT : TaskCT σ)

/-- A CT information variable (sound layer): a variable that supports permutation and copying tasks,
all of which are task-possible via constructor existence. -/
structure InfoVariable (σ : Type u) (CT : TaskCT σ) extends Variable σ where
  /-- Abstract type of permutation codes for this variable. -/
  Perm : Type v
  /-- Task implementing a permutation. -/
  permTask : Perm → Task σ
  /-- Every permutation task is possible. -/
  perm_possible : ∀ p : Perm, CT.possible (permTask p)
  /-- Task implementing copying of the variable. -/
  copyTask : Task σ
  /-- Copying is possible. -/
  copy_possible : CT.possible copyTask

namespace InfoVariable

variable {CT : TaskCT σ}

@[simp] theorem perm_possible' (X : InfoVariable σ CT) (p : X.Perm) :
    CT.possible (X.permTask p) :=
  X.perm_possible p

@[simp] theorem copy_possible' (X : InfoVariable σ CT) :
    CT.possible X.copyTask :=
  X.copy_possible

end InfoVariable

/-- A superinformation medium interface (sound layer).

We model the defining “union not clonable” property as the impossibility of a designated copy task
for a combined variable `XY`. The precise construction of `XY` from `X` and `Y` is left abstract
at this layer (different substrates use different combinations). -/
structure SuperinformationMedium (σ : Type u) (CT : TaskCT σ) where
  /-- First information variable. -/
  X : InfoVariable σ CT
  /-- Second information variable. -/
  Y : InfoVariable σ CT

  /-- A combined variable intended to represent “X ∪ Y”. -/
  XY : Variable σ

  /-- Copy task for the combined variable. -/
  copyXY : Task σ

  /-- Superinformation law: the combined variable cannot be cloned. -/
  no_copyXY : CT.impossible copyXY

namespace SuperinformationMedium

variable {CT : TaskCT σ} (M : SuperinformationMedium σ CT)

theorem no_cloning_union : CT.impossible M.copyXY :=
  M.no_copyXY

end SuperinformationMedium

end TaskCT

end CT
end Constructor
end HeytingLean
