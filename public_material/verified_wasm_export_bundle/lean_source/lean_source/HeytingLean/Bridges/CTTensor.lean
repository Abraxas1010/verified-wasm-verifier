import HeytingLean.Constructor.CT.Core
import HeytingLean.Constructor.CT.Nucleus
import HeytingLean.Bridges.Tensor

/-
# CT ↔ Tensor bridge (minimal scaffold)

Minimal bridge from CT tasks to the existing tensor bridge:
* for a CT nucleus `J` on tasks over `σ` and a LoF tensor model
  `Tensor.Model α`, we define a carrier consisting of CT task-sets
  paired with tensor points;
	* provide a simple encoding from CT tasks into tensor points by
	  duplicating an ambient element across coordinates.

	This scaffold is intentionally modest and serves as a baseline for later
	resource-sensitive CT/tensor semantics.
	-/

namespace HeytingLean
namespace Bridges
namespace CTTensor

open Constructor
open Constructor.CT
open Bridges.Tensor
open HeytingLean.LoF

universe u v

variable {σ : Type u} {α : Type v} [PrimaryAlgebra α]

/-- CT-tensor bridge model: pairs a CT nucleus on tasks over `σ` with a
LoF tensor model over an ambient algebra `α`. -/
structure Model (σ : Type u) (α : Type v) [PrimaryAlgebra α] where
  J : CTNucleus σ
  tensor : Bridges.Tensor.Model α

namespace Model

variable (M : Model σ α)

/-- Carrier of the CT-tensor model: CT task-sets at the nucleus fixed
points paired with tensor points. -/
structure Carrier where
  tasks  : Omega M.J
  weight : Bridges.Tensor.Point α M.tensor.dim

/-- Encode a CT task together with an ambient element `a : α` as a
CT-tensor point by:
* closing `{T}` under the CT nucleus `J` to obtain CT fixed points; and
* duplicating `a` across all tensor coordinates. -/
noncomputable def encode (T : CT.Task σ) (a : α) : Carrier M where
  tasks :=
    ⟨M.J.J {T}, by
      -- Show that `M.J.J {T}` lies in the range of `toNucleus`.
      change ∃ Y, CTNucleus.toNucleus (σ := σ) M.J Y = M.J.J {T}
      refine ⟨M.J.J {T}, ?_⟩
      simp [CTNucleus.toNucleus, CTNucleus.idempotent]⟩
  weight :=
    Bridges.Tensor.Point.mk (fun _ => a)

end Model

end CTTensor
end Bridges
end HeytingLean
