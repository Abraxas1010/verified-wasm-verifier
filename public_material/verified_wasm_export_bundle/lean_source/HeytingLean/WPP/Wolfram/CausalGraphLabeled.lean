import Mathlib.Data.Multiset.UnionInter
import HeytingLean.WPP.Wolfram.CausalGraph

namespace HeytingLean
namespace WPP
namespace Wolfram

/-!
# Labeled / multiplicity-aware causal graphs (SetReplace-style)

The independence result in `ConfluenceCausalInvariance` uses an **unlabeled** causal graph:

> an edge `i → j` exists if some expression is created by event `i` and destroyed by event `j`.

For “higher fidelity” analysis (e.g. counting how many expressions mediate a dependency), it is
useful to keep the **multiset of witnesses**:

`label(i,j) := output(i) ∩ input(j)` (multiset intersection; multiplicities preserved).

This file defines such a labeled causal graph and a forgetful map back to the unlabeled one.
-/

universe u v

/-- A labeled causal graph whose edge-labels are multisets of expressions. -/
structure LabeledCausalGraph (V : Type u) where
  n : Nat
  label : Fin n → Fin n → Multiset (Expr V)

namespace LabeledCausalGraph

variable {V : Type u}

/-- The underlying (unlabeled) edge relation: an edge exists iff its label is nonempty. -/
def edge (g : LabeledCausalGraph V) (i j : Fin g.n) : Prop :=
  g.label i j ≠ 0

/-- Forget labels to obtain a plain `CausalGraph`. -/
def forget (g : LabeledCausalGraph V) : CausalGraph :=
  { n := g.n
    edge := fun i j => g.edge i j }

end LabeledCausalGraph

namespace System

variable {V : Type u} {P : Type v} (sys : System V P)
variable [DecidableEq V]

open System

/-- The multiset of expressions witnessing that `e₁` causes `e₂`. -/
def Event.causeWitnesses (e₁ e₂ : sys.Event) : Multiset (Expr V) :=
  e₁.output ∩ e₂.input

lemma causeWitnesses_ne_zero_iff_causes (e₁ e₂ : sys.Event) :
    e₁.causeWitnesses (sys := sys) e₂ ≠ 0 ↔ e₁.Causes (sys := sys) e₂ := by
  classical
  constructor
  · intro hne
    rcases Multiset.exists_mem_of_ne_zero hne with ⟨x, hx⟩
    have hx' : x ∈ e₁.output ∧ x ∈ e₂.input := (Multiset.mem_inter).1 hx
    exact ⟨x, hx'.1, hx'.2⟩
  · rintro ⟨x, hxOut, hxIn⟩
    intro hzero
    have hx : x ∈ e₁.output ∩ e₂.input := (Multiset.mem_inter).2 ⟨hxOut, hxIn⟩
    have hzero' : e₁.output ∩ e₂.input = 0 := by
      simpa [System.Event.causeWitnesses] using hzero
    have hx0 : x ∈ (0 : Multiset (Expr V)) := by
      -- rewrite the goal (avoid `simp` turning `x ∈ 0` into `False`)
      rw [← hzero']
      exact hx
    exact (Multiset.notMem_zero x hx0).elim

/-- Build the labeled causal graph for a singleway evolution `es`.

Vertices are event indices `Fin es.length`. The label `i → j` is `0` unless `i<j`, in which case
it is `output(i) ∩ input(j)` (multiplicity-aware witnesses). -/
def labeledCausalGraphOf (es : List sys.Event) : LabeledCausalGraph V where
  n := es.length
  label := fun i j =>
    if i.1 < j.1 then
      (es.get i).causeWitnesses (sys := sys) (es.get j)
    else
      0

theorem labeledCausalGraphOf_forget_edge_iff (es : List sys.Event) (i j : Fin es.length) :
    (labeledCausalGraphOf (sys := sys) es).forget.edge i j ↔ (sys.causalGraphOf es).edge i j := by
  classical
  by_cases hlt : i.1 < j.1
  · -- `i<j`: nonempty intersection ↔ `Causes`
    have hcauses :
        (labeledCausalGraphOf (sys := sys) es).label i j ≠ 0 ↔
          (es.get i).Causes (sys := sys) (es.get j) := by
      -- unfold the label for the `i<j` case and apply `causeWitnesses_ne_zero_iff_causes`
      simp [System.labeledCausalGraphOf, hlt, System.causeWitnesses_ne_zero_iff_causes]
    simp [LabeledCausalGraph.forget, LabeledCausalGraph.edge, System.causalGraphOf, hlt, hcauses]
  · -- `¬ i<j`: label is `0` and `causalGraphOf` requires `i<j`, so both are false
    simp [System.labeledCausalGraphOf, LabeledCausalGraph.forget, LabeledCausalGraph.edge,
      System.causalGraphOf, hlt]

theorem labeledCausalGraphOf_forget_iso_causalGraphOf (es : List sys.Event) :
    CausalGraph.Iso (labeledCausalGraphOf (sys := sys) es).forget (sys.causalGraphOf es) := by
  refine ⟨Equiv.refl _, ?_⟩
  intro i j
  simpa using labeledCausalGraphOf_forget_edge_iff (sys := sys) es i j

end System

end Wolfram
end WPP
end HeytingLean
