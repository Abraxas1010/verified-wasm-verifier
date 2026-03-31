import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Basic
import HeytingLean.Constructor.CT.Core
import HeytingLean.Constructor.CT.Nucleus

/-
# Constructor Theory of thermodynamics (work/heat and adiabatic tasks)

Lightweight thermodynamic scaffolding in the CT layer:
* `WorkMedium` / `HeatMedium` wrap CT variables that play the role of
  work and heat media;
* `AdiabaticTask` marks CT tasks intended to be adiabatic for a given
  pair of media;
* composition operators `adiabaticSeq` / `adiabaticPar` witness that
  adiabatic tasks compose at the level of CT syntax;
* `perpetualMotionTask` is a minimal synthetic perpetual-motion task;
* `ThermoAxioms` packages a small set of thermodynamic axioms stating
  that this task is CT‑impossible under a given CT nucleus and substrate;
* `perpetualMotionTask_impossible` restates the impossibility as a
  convenience lemma.

Concrete substrates are expected to refine these interfaces with richer
constraints and connect them to physical semantics.
-/

namespace HeytingLean
namespace Constructor
namespace CT

open Classical

universe u

variable {σ : Type u}

/-- Work medium: a substrate whose states carry a distinguished CT
variable representing work levels. -/
structure WorkMedium (σ : Type u) where
  levels : Variable σ

/-- Heat medium: a substrate whose states carry a distinguished CT
variable representing coarse (macro) configurations used for heat. -/
structure HeatMedium (σ : Type u) where
  macroVar : Variable σ

/-- An adiabatic task over a substrate `σ` for a given work/heat pair.

At this level, `AdiabaticTask` is a thin wrapper around a CT `Task`.  The
intended reading is that the task exchanges only work-like resources in
the associated `WorkMedium` and obeys admissible constraints in the
`HeatMedium`.  Concrete substrates are expected to enrich this with
additional invariants. -/
structure AdiabaticTask (σ : Type u)
    (WM : WorkMedium σ) (HM : HeatMedium σ) where
  /-- Underlying CT task. -/
  task : Task σ

namespace AdiabaticTask

variable {WM : WorkMedium σ} {HM : HeatMedium σ}

/-- Serial composition of adiabatic tasks, combining their underlying CT
tasks via `Task.seq`. -/
def adiabaticSeq (T U : AdiabaticTask σ WM HM) :
    AdiabaticTask σ WM HM :=
  { task := Task.seq T.task U.task }

/-- Parallel composition of adiabatic tasks, combining their underlying
CT tasks via `Task.par`. -/
def adiabaticPar (T U : AdiabaticTask σ WM HM) :
    AdiabaticTask σ WM HM :=
  { task := Task.par T.task U.task }

end AdiabaticTask

/-- A minimal synthetic perpetual-motion task on a substrate `σ`.

This is intentionally schematic: for now it is just a distinguished CT
task built from the empty list of arcs.  Concrete thermodynamic models
are expected to interpret this task as an attempted net work-extracting
cycle without appropriate resource expenditure. -/
def perpetualMotionTask (σ : Type u) : Task σ :=
  { arcs := [] }

/-- Thermodynamic axioms for a CT nucleus on a given substrate.  At this
stage we only record the impossibility of the perpetual-motion task.

Additional axioms (Kelvin/Clausius-style statements, composition of
adiabatic tasks in specific media, etc.) can be added here by concrete
substrates as needed. -/
structure ThermoAxioms (σ : Type u) (J : CTNucleus σ) where
  /-- Perpetual motion is CT‑impossible for the nucleus `J`. -/
  noPerpetualMotion :
    CTNucleus.impossible (J := J) (perpetualMotionTask σ)

/-- Convenience lemma: under thermodynamic axioms `ThermoAxioms`, the
perpetual-motion task is CT‑impossible. -/
theorem perpetualMotionTask_impossible (σ : Type u)
    (J : CTNucleus σ) (axioms : ThermoAxioms σ J) :
    CTNucleus.impossible (J := J) (perpetualMotionTask σ) :=
  axioms.noPerpetualMotion

namespace Examples

open CT
open CT.Examples

/-- Trivial work medium on `Bool` using an empty CT variable. -/
def boolWorkMedium : WorkMedium Bool :=
  { levels := emptyVariable Bool }

/-- Trivial heat medium on `Bool` using an empty CT variable. -/
def boolHeatMedium : HeatMedium Bool :=
  { macroVar := emptyVariable Bool }

/-- Trivial adiabatic task over `Bool` for the trivial work/heat media.
This is a small example of the `AdiabaticTask` wrapper; it does not
assert any thermodynamic properties by itself. -/
def boolAdiabatic :
    AdiabaticTask Bool boolWorkMedium boolHeatMedium :=
  { task := swapTaskBool }

end Examples

end CT
end Constructor
end HeytingLean
