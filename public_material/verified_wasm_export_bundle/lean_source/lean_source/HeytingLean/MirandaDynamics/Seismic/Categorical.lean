import Mathlib.Data.Set.Lattice

import HeytingLean.ClosingTheLoop.Semantics.KernelLaws

/-!
# MirandaDynamics.Seismic: categorical framing (lightweight)

The WIP `miranda_exended.md` describes a “categorical wrapper” layer.

The current seismic implementation is intentionally executable-first:
- `scripts/seismic_bridge.py` produces a JSON bundle with predictions + waveform windows.
- `seismic_validate_demo` (Lean) runs a deterministic STA/LTA detector and emits per-pair results.

For this demo pipeline we treat:
- `P` as the *predicted* reachability proposition for an `(event, station)` pair.
- `k(P)` (kernel) as the *verifiable* reachability proposition derived from observation.

This file provides a small amount of reusable notation for reasoning about
"predicted vs observed" as an interior/kernel operator on a Boolean algebra of sets.

Note: In full generality, Miranda's work is framed in terms of nuclei on Heyting algebras.
Here we keep the framing intentionally minimal and concrete.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Seismic
namespace Categorical

open Set
open HeytingLean.ClosingTheLoop.Semantics

universe u

section

abbrev Pred (α : Type u) := Set α

/-- The Heyting/Boolean "gap" between a proposition and what the kernel verifies. -/
def gap {α : Type u} (k : Kernel (α := Pred α)) (P : Pred α) : Pred α :=
  P \ k P

theorem gap_subset {α : Type u} (k : Kernel (α := Pred α)) (P : Pred α) : gap k P ⊆ P := by
  intro x hx
  exact hx.1

end

end Categorical
end Seismic
end MirandaDynamics
end HeytingLean
