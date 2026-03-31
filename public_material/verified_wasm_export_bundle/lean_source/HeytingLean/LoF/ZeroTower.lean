import Mathlib.Order.Nucleus
import HeytingLean.Bridges.Flow

/-
# Zero Tower

Define a minimal “tower of nuclei” using the order on `Nucleus α` for a
semilattice. We provide named constants

* `R_min` (⊥) — the trivial nucleus,
* `R_osc` (⊥) — a named mid-point, kept equal to `R_min` at the generic
  level, and
* `R_max` (⊤) — the maximal nucleus.

Concrete oscillation-style nuclei live in specialized modules such as
`R_osc_flow` below; here we keep the generic tower as lightweight
bookkeeping.
-/

namespace HeytingLean
namespace LoF

variable {α : Type u} [SemilatticeInf α] [OrderTop α]

/-- Minimal nucleus in the Zero Tower: bottom element of `Nucleus α`. -/
def R_min : Nucleus α := ⊥

/-- Named “oscillation” nucleus at the generic level.

For arbitrary carriers we do not commit to a nontrivial oscillation
closure, so `R_osc` is defined to be `⊥`, matching `R_min`. Concrete
oscillation nuclei are introduced separately for specific carriers
such as flow trajectories. -/
def R_osc : Nucleus α := ⊥

/-- Maximal nucleus in the Zero Tower: top element of `Nucleus α`. -/
def R_max : Nucleus α := ⊤

omit [OrderTop α] in
/-- `R_min` is literally `⊥`, so it is automatically below `R_osc`. -/
lemma R_min_le_R_osc : (R_min : Nucleus α) ≤ R_osc := by
  simp [R_min, R_osc]

/-- Since `R_osc = ⊥` generically, it is bounded above by the maximal nucleus `R_max`. -/
lemma R_osc_le_R_max : (R_osc : Nucleus α) ≤ R_max := by
  simp [R_osc, R_max]

/-- Combining the previous two inclusions shows `R_min ≤ R_max`. -/
lemma R_min_le_R_max : (R_min : Nucleus α) ≤ R_max := by
  exact le_trans R_min_le_R_osc R_osc_le_R_max

end LoF
end HeytingLean

/-!
## Flow specialization (mapping R_osc to a concrete oscillation nucleus)

For the concrete carrier `Set Bridges.FlowTraj`, we expose a specialized
oscillation nucleus built from loop detection. This realizes the intended
`R_osc` semantics in the Flow Lens while keeping the generic `ZeroTower`
definitions available for arbitrary semilattices.
-/

namespace HeytingLean.LoF

open HeytingLean.Bridges

section FlowSpecialization

abbrev FlowCarrier := Set Bridges.FlowTraj

variable (posTol dirCosTol : Float)

def R_osc_flow : Nucleus FlowCarrier :=
  Bridges.Flow.flowNucleusOsc posTol dirCosTol

/-- The oscillation-flow nucleus extends `⊥`, so `R_min` is trivially a lower bound. -/
lemma R_min_le_R_osc_flow : (R_min : Nucleus FlowCarrier) ≤ R_osc_flow posTol dirCosTol := by
  -- ⊥ ≤ any nucleus
  simp [R_min, R_osc_flow]

/-- Any concrete flow nucleus still lies below the maximal nucleus `R_max`. -/
lemma R_osc_flow_le_R_max : (R_osc_flow posTol dirCosTol : Nucleus FlowCarrier) ≤ R_max := by
  -- any nucleus ≤ ⊤
  simp [R_osc_flow, R_max]

variable (kTol vTol : Float)

def R_bounded_flow : Nucleus FlowCarrier :=
  Bridges.Flow.flowNucleusBounded kTol vTol

/-- Bounded-flow nuclei include the trivial re-entry, so `R_min ≤ R_bounded_flow`. -/
lemma R_min_le_R_bounded_flow : (R_min : Nucleus FlowCarrier) ≤ R_bounded_flow kTol vTol := by
  simp [R_min, R_bounded_flow]

/-- Like every nucleus, `R_bounded_flow` is dominated by `R_max`. -/
lemma R_bounded_flow_le_R_max : (R_bounded_flow kTol vTol : Nucleus FlowCarrier) ≤ R_max := by
  simp [R_bounded_flow, R_max]

end FlowSpecialization

end HeytingLean.LoF
