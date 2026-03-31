import HeytingLean.ATheory.AssemblyCore
import HeytingLean.ATheory.CopyNumberSelection

/-
# Assembly-based complexity observables

This module packages existing Assembly Theory quantities into a small
metrics layer:

* an object-level complexity given by the Assembly index (or birth index);
* a per-object Assembly score combining index and copy-number weight;
	* an ensemble-level Assembly quantity over a finite set of objects.

	All definitions are thin wrappers around the core `ATheory` layer; no
	new axioms are introduced and there are no dummy semantics.
	-/

namespace HeytingLean
namespace Metrics
namespace AssemblyComplexity

open HeytingLean.ATheory

universe u

/-- Object-level complexity for Assembly Theory: the syntactic index of an
object `o` with respect to a rule set `R`.  This is just `syntacticIndex`
re-exposed with a metrics-oriented name. -/
def objectIndex {α : Type u} [DecidableEq α] (R : Rules α) (o : Obj α) : Nat :=
  syntacticIndex R o

/-- Alias emphasising the “birth-time” reading of the Assembly index. -/
def birthIndex {α : Type u} [DecidableEq α] (R : Rules α) (o : Obj α) : Nat :=
  objectIndex R o

/-- Configuration for Assembly-based complexity on a finite type `V`.

* `idx` is typically instantiated by an Assembly index (or birth index);
* `copy` provides raw copy numbers and a secondary weight.

This structure is deliberately lightweight so that concrete models can
decide how to obtain `idx` (e.g. via `assemblyIndex` on an associated
Assembly object). -/
structure Config (V : Type u) where
  idx  : V → Nat
  copy : CopyNumber V

namespace Config

variable {V : Type u} (cfg : Config V)

/-- Per-object Assembly score induced by a complexity configuration.

This uses the `Assembly` functional from `CopyNumberSelection`, combining
the index `idx v` with the secondary weight `μ v`. -/
noncomputable def objectScore (v : V) : ℝ :=
  Assembly cfg.idx cfg.copy.μ v

/-- Ensemble-level Assembly complexity over a finite set `vset`, using
the raw copy numbers from `copy.n`.  This is a direct application of
`AssemblyEnsemble`. -/
noncomputable def ensembleScore (vset : Finset V) : ℝ :=
  AssemblyEnsemble cfg.idx cfg.copy.n vset

end Config

end AssemblyComplexity
end Metrics
end HeytingLean
