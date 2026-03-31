import HeytingLean.Bridges.Clifford

/-
# Visual.OperatorDiagram

A small syntax of unary operator/Clifford diagrams over the Clifford bridge
carrier, together with an evaluation function into endomorphisms on that
carrier.

The constructors expose a subset of the existing Clifford bridge operations:

* the identity operator;
* the nucleus-induced projector `project`;
* stage-style orthocomplement, collapse, expand, and Occam operations;
* composition of such operators.

The goal is to provide a compositional, Lean-level representation of
operator-style diagrams suitable for later visualization and for stating
soundness properties of composed operations.
-/

namespace HeytingLean
namespace Visual
namespace Clifford

open HeytingLean.Bridges
open HeytingLean.LoF

universe u

variable {α : Type u} [PrimaryAlgebra α]

/-- Unary operator diagrams built from Clifford bridge primitives. -/
inductive Diagram (M : Bridges.Clifford.Model α) : Type u where
  | id :
      Diagram M
  | project :
      Diagram M
  | stageOrthocomplement :
      Diagram M
  | stageCollapseAt (n : Nat) :
      Diagram M
  | stageExpandAt (n : Nat) :
      Diagram M
  | stageOccam :
      Diagram M
  | comp (f g : Diagram M) :
      Diagram M

namespace Diagram

variable {M : Bridges.Clifford.Model α}

 /-- Evaluate an operator diagram as an endomorphism on the Clifford
carrier.

Marked `noncomputable` because the underlying Clifford bridge operations are
noncomputable. -/
noncomputable def eval : Diagram M → M.Carrier → M.Carrier
  | id => fun p => p
  | project => fun p => M.project p
  | stageOrthocomplement => fun p => M.stageOrthocomplement p
  | stageCollapseAt n => fun p => M.stageCollapseAt n p
  | stageExpandAt n => fun p => M.stageExpandAt n p
  | stageOccam => fun p => M.stageOccam p
  | comp f g => fun p => eval g (eval f p)

@[simp] lemma eval_id (p : M.Carrier) :
    eval (Diagram.id (M := M)) p = p :=
  rfl

@[simp] lemma eval_project (p : M.Carrier) :
    eval (Diagram.project (M := M)) p = M.project p :=
  rfl

@[simp] lemma eval_stageOrthocomplement (p : M.Carrier) :
    eval (Diagram.stageOrthocomplement (M := M)) p =
      M.stageOrthocomplement p :=
  rfl

@[simp] lemma eval_stageCollapseAt (n : Nat) (p : M.Carrier) :
    eval (Diagram.stageCollapseAt (M := M) n) p =
      M.stageCollapseAt n p :=
  rfl

@[simp] lemma eval_stageExpandAt (n : Nat) (p : M.Carrier) :
    eval (Diagram.stageExpandAt (M := M) n) p =
      M.stageExpandAt n p :=
  rfl

@[simp] lemma eval_stageOccam (p : M.Carrier) :
    eval (Diagram.stageOccam (M := M)) p =
      M.stageOccam p :=
  rfl

@[simp] lemma eval_comp (f g : Diagram M) (p : M.Carrier) :
    eval (Diagram.comp f g) p =
      eval g (eval f p) :=
  rfl

end Diagram

end Clifford
end Visual
end HeytingLean
