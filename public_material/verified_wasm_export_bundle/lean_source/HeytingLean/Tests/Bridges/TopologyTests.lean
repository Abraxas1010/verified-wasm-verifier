import HeytingLean.Bridges.Topology
import HeytingLean.Bridges.Tensor
import HeytingLean.Bridges.Graph
import HeytingLean.Bridges.Clifford
import HeytingLean.Contracts.RoundTrip

/-!
# Topology Lens Fidelity Tests

Following the Lens Testing Methodology:
1. Start from known topological objects (closed sets, closure operator)
2. Transform to R.Omega (LoF/Heyting fixed points)
3. Transform back to verify fidelity

## Test Tiers

- Tier 1: Structural round-trips (⊤, ⊥, arbitrary)
- Tier 2: Domain-specific (closure properties, closed set preservation)
- Tier 3: Cross-lens with Tensor, Graph, Clifford
- Tier 4: Concrete topological objects (Euler boundary, primordial)
-/

namespace HeytingLean
namespace Tests
namespace Bridges
namespace TopologyTests

open HeytingLean.LoF
open HeytingLean.Contracts
open HeytingLean.Bridges

universe u

variable {α : Type u} [PrimaryAlgebra α]
variable (R : Reentry α)

/-! ## Tier 1: Structural Round-Trip Tests -/

section Tier1_Structural

variable (M : Topology.Model α)

/-- Round-trip on ⊤ preserves top element. -/
theorem topology_top_roundtrip :
    M.contract.decode (M.contract.encode (⊤ : M.R.Omega)) = ⊤ :=
  M.contract.round ⊤

/-- Round-trip on ⊥ preserves bottom element. -/
theorem topology_bot_roundtrip :
    M.contract.decode (M.contract.encode (⊥ : M.R.Omega)) = ⊥ :=
  M.contract.round ⊥

/-- Round-trip on arbitrary element (the contract law). -/
theorem topology_arbitrary_roundtrip (a : M.R.Omega) :
    M.contract.decode (M.contract.encode a) = a :=
  M.contract.round a

/-- The logical shadow of an encoded element equals R applied to it. -/
theorem topology_logical_shadow (a : M.R.Omega) :
    M.logicalShadow (M.contract.encode a) = M.R a :=
  M.logicalShadow_encode a

end Tier1_Structural

/-! ## Tier 2: Domain-Specific Topological Properties -/

section Tier2_DomainSpecific

variable (M : Topology.Model α)

/-- Encoded elements from R.Omega are always closed (R-fixed). -/
theorem topology_encode_is_closed (a : M.R.Omega) :
    M.isClosed (M.encode a) :=
  M.encode_isClosed a

/-- Closure operator is idempotent: cl(cl(x)) = cl(x). -/
theorem topology_closure_idempotent (x : α) :
    M.closure (M.closure x) = M.closure x :=
  M.closure_idempotent x

/-- Closure operator preserves finite meets: cl(x ∩ y) = cl(x) ∩ cl(y). -/
theorem topology_closure_preserves_inf (x y : α) :
    M.closure (x ⊓ y) = M.closure x ⊓ M.closure y :=
  M.closure_inf x y

/-- Closure is inflationary: x ≤ cl(x). -/
theorem topology_closure_inflationary (x : α) :
    x ≤ M.closure x :=
  M.closure_inflationary x

/-- Closed sets are exactly the R-fixed points. -/
theorem topology_closed_iff_fixed (x : α) :
    M.isClosed x ↔ M.R x = x :=
  M.isClosed_iff_fixed x

/-- The closure of a meet is closed. -/
theorem topology_closure_inf_is_closed (x y : α) :
    M.isClosed (M.closure (x ⊓ y)) :=
  M.isClosed_closure_inf x y

end Tier2_DomainSpecific

/-! ## Tier 3: Cross-Lens Preservation Tests -/

section Tier3_CrossLens

/-- Helper: Create a Topology model from a Reentry. -/
noncomputable def topologyModel (R : Reentry α) : Topology.Model α :=
  { R := R }

/-- Helper: Create a Tensor model from a Reentry. -/
noncomputable def tensorModel (R : Reentry α) (dim : ℕ) : Tensor.Model α :=
  { dim := dim, R := R }

/-- Helper: Create a Graph model from a Reentry. -/
noncomputable def graphModel (R : Reentry α) : Graph.Model α :=
  { R := R }

/-- Helper: Create a Clifford model from a Reentry. -/
noncomputable def cliffordModel (R : Reentry α) : Clifford.Model α :=
  { R := R }

variable (dim : ℕ)

/-- Topology ↔ Tensor cross-lens preservation. -/
theorem topology_tensor_cross (a : R.Omega) :
    (topologyModel R).contract.decode
      ((topologyModel R).contract.encode
        ((tensorModel R dim).contract.decode
          ((tensorModel R dim).contract.encode a))) = a := by
  rw [(tensorModel R dim).contract.round a]
  rw [(topologyModel R).contract.round a]

/-- Tensor ↔ Topology cross-lens preservation (reverse direction). -/
theorem tensor_topology_cross (a : R.Omega) :
    (tensorModel R dim).contract.decode
      ((tensorModel R dim).contract.encode
        ((topologyModel R).contract.decode
          ((topologyModel R).contract.encode a))) = a := by
  rw [(topologyModel R).contract.round a]
  rw [(tensorModel R dim).contract.round a]

/-- Topology ↔ Graph cross-lens preservation. -/
theorem topology_graph_cross (a : R.Omega) :
    (topologyModel R).contract.decode
      ((topologyModel R).contract.encode
        ((graphModel R).contract.decode
          ((graphModel R).contract.encode a))) = a := by
  rw [(graphModel R).contract.round a]
  rw [(topologyModel R).contract.round a]

/-- Graph ↔ Topology cross-lens preservation (reverse direction). -/
theorem graph_topology_cross (a : R.Omega) :
    (graphModel R).contract.decode
      ((graphModel R).contract.encode
        ((topologyModel R).contract.decode
          ((topologyModel R).contract.encode a))) = a := by
  rw [(topologyModel R).contract.round a]
  rw [(graphModel R).contract.round a]

/-- Topology ↔ Clifford cross-lens preservation. -/
theorem topology_clifford_cross (a : R.Omega) :
    (topologyModel R).contract.decode
      ((topologyModel R).contract.encode
        ((cliffordModel R).contract.decode
          ((cliffordModel R).contract.encode a))) = a := by
  rw [(cliffordModel R).contract.round a]
  rw [(topologyModel R).contract.round a]

/-- Clifford ↔ Topology cross-lens preservation (reverse direction). -/
theorem clifford_topology_cross (a : R.Omega) :
    (cliffordModel R).contract.decode
      ((cliffordModel R).contract.encode
        ((topologyModel R).contract.decode
          ((topologyModel R).contract.encode a))) = a := by
  rw [(topologyModel R).contract.round a]
  rw [(cliffordModel R).contract.round a]

/-- Full 4-lens cycle: Topology → Tensor → Graph → Clifford → Topology preserves. -/
theorem four_lens_cycle_preserves (a : R.Omega) :
    (topologyModel R).contract.decode
      ((topologyModel R).contract.encode
        ((cliffordModel R).contract.decode
          ((cliffordModel R).contract.encode
            ((graphModel R).contract.decode
              ((graphModel R).contract.encode
                ((tensorModel R dim).contract.decode
                  ((tensorModel R dim).contract.encode
                    ((topologyModel R).contract.decode
                      ((topologyModel R).contract.encode a))))))))) = a := by
  rw [(topologyModel R).contract.round a]
  rw [(tensorModel R dim).contract.round a]
  rw [(graphModel R).contract.round a]
  rw [(cliffordModel R).contract.round a]
  rw [(topologyModel R).contract.round a]

/-- Logical shadow is the same through Topology and Graph lenses. -/
theorem topology_graph_shadow_eq (a : R.Omega) :
    interiorized R (topologyModel R).contract ((topologyModel R).contract.encode a) =
    interiorized R (graphModel R).contract ((graphModel R).contract.encode a) := by
  simp only [interiorized_id]

/-- Logical shadow is the same through all four lenses. -/
theorem all_four_shadows_eq (a : R.Omega) :
    interiorized R (topologyModel R).contract ((topologyModel R).contract.encode a) =
    interiorized R (tensorModel R dim).contract ((tensorModel R dim).contract.encode a) ∧
    interiorized R (tensorModel R dim).contract ((tensorModel R dim).contract.encode a) =
    interiorized R (graphModel R).contract ((graphModel R).contract.encode a) ∧
    interiorized R (graphModel R).contract ((graphModel R).contract.encode a) =
    interiorized R (cliffordModel R).contract ((cliffordModel R).contract.encode a) := by
  simp only [interiorized_id, and_self]

end Tier3_CrossLens

/-! ## Tier 4: Concrete Topological Objects -/

section Tier4_ConcreteObjects

variable (M : Topology.Model α)

/-- The Euler boundary (primordial fixed point) encodes to the primordial element.
This is a concrete topological object: the minimal nontrivial closed set. -/
theorem euler_boundary_encodes_to_primordial :
    M.encode M.R.eulerBoundary = M.R.primordial :=
  M.encode_eulerBoundary

/-- The Euler boundary round-trips correctly. -/
theorem euler_boundary_roundtrip :
    M.contract.decode (M.contract.encode M.R.eulerBoundary) = M.R.eulerBoundary :=
  M.contract.round M.R.eulerBoundary

/-- The primordial element is closed (it's an R-fixed point by definition). -/
theorem primordial_is_closed :
    M.isClosed M.R.primordial := by
  simp only [Topology.Model.isClosed, Topology.Model.closure]
  exact M.R.primordial_mem

/-- The counter element is closed (it's an R-fixed point by definition). -/
theorem counter_is_closed :
    M.isClosed M.R.counter := by
  simp only [Topology.Model.isClosed, Topology.Model.closure]
  exact M.R.counter_mem

/-- Top element round-trip preserves top (concrete test). -/
theorem top_concrete_roundtrip :
    M.contract.decode (M.contract.encode (⊤ : M.R.Omega)) = ⊤ :=
  M.contract.round ⊤

/-- Bottom element round-trip preserves bottom (concrete test). -/
theorem bot_concrete_roundtrip :
    M.contract.decode (M.contract.encode (⊥ : M.R.Omega)) = ⊥ :=
  M.contract.round ⊥

/-- Meet of primordial and counter is bottom (orthogonality test). -/
theorem primordial_counter_orthogonal :
    M.R.primordial ⊓ M.R.counter = ⊥ :=
  M.R.orthogonal

end Tier4_ConcreteObjects

/-! ## Summary

### Tests Completed

**Tier 1 (Structural)**: 4 tests
- top_roundtrip ✓
- bot_roundtrip ✓
- arbitrary_roundtrip ✓
- logical_shadow ✓

**Tier 2 (Domain-Specific)**: 6 tests
- encode_is_closed ✓
- closure_idempotent ✓
- closure_preserves_inf ✓
- closure_inflationary ✓
- closed_iff_fixed ✓
- closure_inf_is_closed ✓

**Tier 3 (Cross-Lens)**: 9 tests
- topology_tensor_cross ✓
- tensor_topology_cross ✓
- topology_graph_cross ✓
- graph_topology_cross ✓
- topology_clifford_cross ✓
- clifford_topology_cross ✓
- four_lens_cycle_preserves ✓
- topology_graph_shadow_eq ✓
- all_four_shadows_eq ✓

**Tier 4 (Concrete Objects)**: 7 tests
- euler_boundary_encodes_to_primordial ✓
- euler_boundary_roundtrip ✓
- primordial_is_closed ✓
- counter_is_closed ✓
- top_concrete_roundtrip ✓
- bot_concrete_roundtrip ✓
- primordial_counter_orthogonal ✓

**Total**: 26 tests across 4 tiers
-/

end TopologyTests
end Bridges
end Tests
end HeytingLean
