import HeytingLean.WPP.Wolfram.CausalGraph
import HeytingLean.WPP.Wolfram.RewriteFresh

namespace HeytingLean
namespace WPP
namespace Wolfram

/-!
# Causal graphs for `SystemFresh` (explicit fresh assignments)

For the fresh-vertex semantics (`SystemFresh`), an event's output depends on the chosen
fresh assignment `τ`. For causal-graph construction we therefore work with *concrete*
events that carry both:

* a rule index + match substitution `σ` (as in `SystemFresh.Event`), and
* an explicit fresh assignment `τ`.

This matches SetReplace-style causality:

> event A causes event B if some expression created by A is destroyed by B

Here we keep the same simple witness notion used in `CausalGraph.lean`:
`x ∈ output(A) ∧ x ∈ input(B)`.
-/

universe u v

namespace SystemFresh

variable {V : Type u} {P : Type v} (sys : SystemFresh V P)
variable [DecidableEq V]

open SystemFresh

/-- A concrete event for `SystemFresh`: match data plus an explicit fresh assignment. -/
structure ConcreteEvent (sys : SystemFresh V P) where
  e : sys.Event
  τ : Fin e.rule.nFresh → V

namespace ConcreteEvent

variable {sys}

@[simp] def input (ce : sys.ConcreteEvent) : HGraph V :=
  ce.e.input

@[simp] def output (ce : sys.ConcreteEvent) : HGraph V :=
  ce.e.rule.instRhs ce.e.σ ce.τ

/-- Causal dependency (SetReplace-style witness): some expression is in `output` of the first
and in `input` of the second. -/
def Causes (ce₁ ce₂ : sys.ConcreteEvent) : Prop :=
  ∃ x, x ∈ ce₁.output ∧ x ∈ ce₂.input

end ConcreteEvent

/-- Build the causal graph of a concrete singleway trace. -/
def causalGraphOf (es : List sys.ConcreteEvent) : CausalGraph where
  n := es.length
  edge := fun i j =>
    i.1 < j.1 ∧ (es.get i).Causes (sys := sys) (es.get j)

end SystemFresh

end Wolfram
end WPP
end HeytingLean

