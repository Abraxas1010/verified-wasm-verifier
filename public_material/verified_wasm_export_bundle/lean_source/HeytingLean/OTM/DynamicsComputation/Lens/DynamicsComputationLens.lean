import Mathlib.Data.Set.Lattice
import HeytingLean.OTM.DynamicsComputation.DynamicalSystem

namespace HeytingLean
namespace OTM
namespace DynamicsComputation
namespace Lens

universe u v

/--
Round-trip lens between a dynamics state space `X` and a computation state space `Y`.
-/
structure DynamicsComputationLens (X : Type u) (Y : Type v) where
  encode : X → Y
  decode : Y → X
  roundTrip_X : ∀ x : X, decode (encode x) = x

namespace DynamicsComputationLens

variable {X : Type u} {Y : Type v} (L : DynamicsComputationLens X Y)

def push (U : Set X) : Set Y := L.encode '' U
def pull (V : Set Y) : Set X := L.decode '' V

theorem mem_push_iff {U : Set X} {y : Y} :
    y ∈ L.push U ↔ ∃ x, x ∈ U ∧ L.encode x = y := Iff.rfl

theorem mem_pull_iff {V : Set Y} {x : X} :
    x ∈ L.pull V ↔ ∃ y, y ∈ V ∧ L.decode y = x := Iff.rfl

theorem subset_pull_push (U : Set X) : U ⊆ L.pull (L.push U) := by
  intro x hx
  refine ⟨L.encode x, ?_, ?_⟩
  · exact ⟨x, hx, rfl⟩
  · exact L.roundTrip_X x

theorem roundTrip_elem (x : X) : L.decode (L.encode x) = x :=
  L.roundTrip_X x

/--
Compatibility witness saying a lens preserves time evolution between two
discrete dynamical systems.
-/
structure FlowCompatible (DX : DynamicalSystem X) (DY : DynamicalSystem Y) : Prop where
  encode_flow : ∀ n x, L.encode (DX.flow n x) = DY.flow n (L.encode x)

variable {L}
variable {DX : DynamicalSystem X} {DY : DynamicalSystem Y}

theorem reaches_encode (hflow : L.FlowCompatible DX DY) {x x' : X}
    (hxx' : DX.reaches x x') :
    DY.reaches (L.encode x) (L.encode x') := by
  rcases hxx' with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  calc
    DY.flow n (L.encode x) = L.encode (DX.flow n x) := by
      simpa using (hflow.encode_flow n x).symm
    _ = L.encode x' := by simpa [hn]

theorem equilibrium_encode (hflow : L.FlowCompatible DX DY) {x : X}
    (hx : x ∈ DX.equilibriumSet) :
    L.encode x ∈ DY.equilibriumSet := by
  intro n
  calc
    DY.flow n (L.encode x) = L.encode (DX.flow n x) := by
      simpa using (hflow.encode_flow n x).symm
    _ = L.encode x := by simpa [hx n]

theorem push_reachabilityClosure_subset (hflow : L.FlowCompatible DX DY) (U : Set X) :
    L.push (DX.reachabilityClosure U) ⊆ DY.reachabilityClosure (L.push U) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  rcases hx with ⟨n, hnU⟩
  refine ⟨n, ?_⟩
  exact ⟨DX.flow n x, hnU, by simpa using hflow.encode_flow n x⟩

theorem push_equilibrium_subset (hflow : L.FlowCompatible DX DY) :
    L.push DX.equilibriumSet ⊆ DY.equilibriumSet := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact equilibrium_encode (L := L) hflow hx

end DynamicsComputationLens

end Lens
end DynamicsComputation
end OTM
end HeytingLean
