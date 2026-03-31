import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Basic

/-!
# QuantumActiveInference.TensorControl

Minimal tensor-network control-flow scaffolding.

This module is *not* a full tensor-network library. It provides:
- a tiny “indexed tensor” carrier (function-valued),
- a contraction operator (finite dot product),
- a `TensorNetwork` wrapper used as a control-flow hook.
-/

namespace HeytingLean
namespace QuantumActiveInference

open scoped BigOperators

/-- A tiny indexed tensor: entries indexed by `ι`. -/
structure IndexedTensor (ι : Type) (α : Type) where
  entry : ι → α

namespace IndexedTensor

variable {ι : Type} {α : Type}

/-- Contract two tensors by summing pointwise products (finite dot product). -/
def contract [Fintype ι] [CommSemiring α] (a b : IndexedTensor ι α) : α :=
  ∑ i : ι, a.entry i * b.entry i

theorem contract_comm [Fintype ι] [CommSemiring α] (a b : IndexedTensor ι α) :
    contract a b = contract b a := by
  classical
  simp [contract, mul_comm]

end IndexedTensor

/-- A minimal tensor network: a finite list of tensors together with a designated “control” tensor. -/
structure TensorNetwork (ι : Type) (α : Type) where
  nodes : List (IndexedTensor ι α)
  control : IndexedTensor ι α

/-- A control-flow hook tying a state-transition function to a tensor network. -/
structure ControlFlowTN (ι : Type) (α σ : Type) where
  net : TensorNetwork ι α
  step : σ → σ
  coherent : Prop := True

end QuantumActiveInference
end HeytingLean
