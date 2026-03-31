import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import HeytingLean.WPP.Wolfram.Rewrite
import HeytingLean.WPP.Wolfram.RewriteFresh

namespace HeytingLean
namespace WPP
namespace Wolfram

/-!
# When are matches injective? (simple-hypergraph conditions)

Wolfram's SetReplace-style rewriting permits **non-injective** matches `σ : P → V` in general.
However, under a "simple hypergraph" invariant (no repeated vertices *within* any edge), certain
rules force injectivity.

This file makes that precise:
- If a state `s` has only nodup edges, and an instantiated LHS edge `σ(ex)` appears in `s`,
  then `σ` is injective on the vertices of `ex`.
- In particular, if `P = Fin n` and the LHS contains the edge `List.finRange n`, then any
  applicable match is globally injective.
-/

namespace HGraph

variable {V : Type u}

/-- A "simple hypergraph" condition: every edge has no repeated vertices. -/
def SimpleEdges (g : HGraph V) : Prop :=
  ∀ e ∈ g, (e : Expr V).Nodup

end HGraph

namespace System
namespace Event

variable {V : Type u} {P : Type v} {sys : System V P}

lemma injectiveOn_of_applicable_of_mem_lhs [DecidableEq V] (e : sys.Event) (s : HGraph V)
    (hs : HGraph.SimpleEdges (V := V) s) (happ : e.Applicable (sys := sys) s)
    {ex : Expr P} (hex : ex ∈ (sys.rules.get e.idx).lhs) :
    ∀ x ∈ ex, ∀ y ∈ ex, e.σ x = e.σ y → x = y := by
  classical
  -- `σ(ex)` is one of the instantiated input edges.
  have hexInput : Expr.rename e.σ ex ∈ e.input (sys := sys) := by
    simpa [System.Event.input, Rule.instLhs, Rule.inst, HGraph.rename] using
      (Multiset.mem_map_of_mem (Expr.rename e.σ) hex)
  -- Applicability makes it a member of the current state.
  have hexS : Expr.rename e.σ ex ∈ s := Multiset.mem_of_le happ hexInput
  -- "Simple edges" gives nodup of the mapped edge, hence injectivity on `ex`.
  have hnodup : (Expr.rename e.σ ex).Nodup := hs _ hexS
  intro x hx y hy hxy
  exact List.inj_on_of_nodup_map (f := e.σ) (l := ex) (by simpa [Expr.rename] using hnodup) hx hy hxy

theorem injective_of_applicable_of_finRange_mem_lhs [DecidableEq V] {n : Nat}
    (sys : System V (Fin n)) (e : sys.Event) (s : HGraph V)
    (hs : HGraph.SimpleEdges (V := V) s) (happ : e.Applicable (sys := sys) s)
    (hfin : List.finRange n ∈ (sys.rules.get e.idx).lhs) :
    Function.Injective e.σ := by
  intro i j hij
  have hinjOn :=
    injectiveOn_of_applicable_of_mem_lhs (sys := sys) (e := e) (s := s) hs happ (ex := List.finRange n) hfin
  exact hinjOn i (List.mem_finRange i) j (List.mem_finRange j) hij

end Event
end System

namespace SystemFresh
namespace Event

variable {V : Type u} {P : Type v} {sys : SystemFresh V P}

lemma injectiveOn_of_applicable_of_mem_lhs [DecidableEq V] (e : sys.Event) (s : HGraph V)
    (hs : HGraph.SimpleEdges (V := V) s) (happ : e.Applicable s)
    {ex : Expr P} (hex : ex ∈ (e.rule).lhs) :
    ∀ x ∈ ex, ∀ y ∈ ex, e.σ x = e.σ y → x = y := by
  classical
  -- `σ(ex)` is one of the instantiated input edges.
  have hexInput : Expr.rename e.σ ex ∈ e.input := by
    simpa [SystemFresh.Event.input, RuleFresh.instLhs, HGraph.rename] using
      (Multiset.mem_map_of_mem (Expr.rename e.σ) hex)
  -- Applicability makes it a member of the current state.
  have hexS : Expr.rename e.σ ex ∈ s := Multiset.mem_of_le happ hexInput
  -- "Simple edges" gives nodup of the mapped edge, hence injectivity on `ex`.
  have hnodup : (Expr.rename e.σ ex).Nodup := hs _ hexS
  intro x hx y hy hxy
  exact List.inj_on_of_nodup_map (f := e.σ) (l := ex) (by simpa [Expr.rename] using hnodup) hx hy hxy

theorem injective_of_applicable_of_finRange_mem_lhs [DecidableEq V] {n : Nat}
    (sys : SystemFresh V (Fin n)) (e : sys.Event) (s : HGraph V)
    (hs : HGraph.SimpleEdges (V := V) s) (happ : e.Applicable s)
    (hfin : List.finRange n ∈ (e.rule).lhs) :
    Function.Injective e.σ := by
  intro i j hij
  have hinjOn :=
    injectiveOn_of_applicable_of_mem_lhs (sys := sys) (e := e) (s := s) hs happ (ex := List.finRange n) hfin
  exact hinjOn i (List.mem_finRange i) j (List.mem_finRange j) hij

end Event
end SystemFresh

end Wolfram
end WPP
end HeytingLean

