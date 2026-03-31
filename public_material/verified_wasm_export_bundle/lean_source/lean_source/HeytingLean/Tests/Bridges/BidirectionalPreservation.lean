import HeytingLean.Bridges.Tensor
import HeytingLean.Bridges.Graph
import HeytingLean.Bridges.Clifford
import HeytingLean.LoF.Nucleus
import HeytingLean.Contracts.RoundTrip

/-!
# Bidirectional Information Preservation Tests

This module proves **general theorems** about the `RoundTrip` contract interface,
then instantiates them for specific lens combinations.

## Architecture

```
Tensor ←─encode/decode─► R.Omega ←─encode/decode─► Graph
                            ▲
                            │
                     encode/decode
                            │
                            ▼
                        Clifford
```

## Key Insight

Instead of proving specific theorems for each lens pair, we prove theorems
about the `RoundTrip` interface. These automatically apply to ALL lenses.

## Generalized Theorems

1. `cross_lens_preserves`: Any two lenses preserve R.Omega through cross-transformation
2. `chain_preserves`: Any chain of lens transformations preserves R.Omega
3. `logical_shadow_universal`: All lenses produce the same logical shadow R(a)
-/

namespace HeytingLean
namespace Tests
namespace Bridges

open HeytingLean.LoF
open HeytingLean.Contracts
open HeytingLean.Bridges

universe u v w

variable {α : Type u} [PrimaryAlgebra α]
variable (R : Reentry α)

/-! ## General RoundTrip Theorems -/

section GeneralTheorems

variable {C1 : Type v} {C2 : Type w}
variable (contract1 : RoundTrip R C1)
variable (contract2 : RoundTrip R C2)

/-- **Core theorem**: Cross-lens transformation preserves R.Omega content.

Given any two lenses with RoundTrip contracts over the same nucleus R,
encoding into lens 2, decoding back to R.Omega, then encoding into lens 1
and decoding, recovers the original element.

This is the fundamental bidirectional preservation property. -/
theorem cross_lens_preserves (a : R.Omega) :
    contract1.decode (contract1.encode (contract2.decode (contract2.encode a))) = a := by
  rw [contract2.round a]  -- decode₂ (encode₂ a) = a
  rw [contract1.round a]  -- decode₁ (encode₁ a) = a

/-- Cross-lens in reverse direction also preserves. -/
theorem cross_lens_preserves_rev (a : R.Omega) :
    contract2.decode (contract2.encode (contract1.decode (contract1.encode a))) = a := by
  rw [contract1.round a]
  rw [contract2.round a]

/-- The R.Omega element recovered through any lens is the same. -/
theorem omega_recovered_eq (a : R.Omega) :
    contract1.decode (contract1.encode a) = contract2.decode (contract2.encode a) := by
  rw [contract1.round a, contract2.round a]

end GeneralTheorems

/-! ## Chain Preservation -/

section ChainPreservation

variable {C1 : Type*} {C2 : Type*} {C3 : Type*}
variable (contract1 : RoundTrip R C1)
variable (contract2 : RoundTrip R C2)
variable (contract3 : RoundTrip R C3)

/-- Three-lens chain: C1 → C2 → C3 → C1 preserves content. -/
theorem chain3_preserves (a : R.Omega) :
    contract1.decode (contract1.encode
      (contract3.decode (contract3.encode
        (contract2.decode (contract2.encode
          (contract1.decode (contract1.encode a))))))) = a := by
  rw [contract1.round a]
  rw [contract2.round a]
  rw [contract3.round a]
  rw [contract1.round a]

/-- Any chain of encode/decode pairs through R.Omega preserves content.

The key insight: each `decode (encode a) = a` by the round-trip law,
so any number of compositions still yields `a`. -/
theorem chain_principle (a : R.Omega) :
    -- After any encode/decode pair, we're back to the same R.Omega element
    contract1.decode (contract1.encode a) = a ∧
    contract2.decode (contract2.encode a) = a ∧
    contract3.decode (contract3.encode a) = a :=
  ⟨contract1.round a, contract2.round a, contract3.round a⟩

end ChainPreservation

/-! ## Logical Shadow Universality -/

section LogicalShadow

variable {C1 : Type*} {C2 : Type*}
variable (contract1 : RoundTrip R C1)
variable (contract2 : RoundTrip R C2)

/-- All lenses produce the same logical shadow: R(a).

The logical shadow (interiorized value) is independent of the lens representation. -/
theorem logical_shadow_universal (a : R.Omega) :
    interiorized R contract1 (contract1.encode a) =
    interiorized R contract2 (contract2.encode a) := by
  simp only [interiorized_id]

/-- The logical shadow equals R applied to the element. -/
theorem logical_shadow_eq_nucleus (a : R.Omega) :
    interiorized R contract1 (contract1.encode a) = R a := by
  exact interiorized_id R contract1 a

end LogicalShadow

/-! ## Instantiation for Specific Lenses -/

section Instantiation

-- Create models sharing the same nucleus R
noncomputable def tensorModel (R : Reentry α) (dim : ℕ) : Tensor.Model α :=
  { dim := dim, R := R }

noncomputable def graphModel (R : Reentry α) : Graph.Model α :=
  { R := R }

noncomputable def cliffordModel (R : Reentry α) : Clifford.Model α :=
  { R := R }

variable (dim : ℕ)

-- Instantiate the general theorems for specific lens pairs

/-- Tensor ↔ Graph preservation (from general theorem). -/
theorem tensor_graph_preserves (a : R.Omega) :
    (tensorModel R dim).contract.decode
      ((tensorModel R dim).contract.encode
        ((graphModel R).contract.decode
          ((graphModel R).contract.encode a))) = a :=
  cross_lens_preserves R (tensorModel R dim).contract (graphModel R).contract a

/-- Graph ↔ Tensor preservation (from general theorem). -/
theorem graph_tensor_preserves (a : R.Omega) :
    (graphModel R).contract.decode
      ((graphModel R).contract.encode
        ((tensorModel R dim).contract.decode
          ((tensorModel R dim).contract.encode a))) = a :=
  cross_lens_preserves R (graphModel R).contract (tensorModel R dim).contract a

/-- Tensor ↔ Clifford preservation (from general theorem). -/
theorem tensor_clifford_preserves (a : R.Omega) :
    (tensorModel R dim).contract.decode
      ((tensorModel R dim).contract.encode
        ((cliffordModel R).contract.decode
          ((cliffordModel R).contract.encode a))) = a :=
  cross_lens_preserves R (tensorModel R dim).contract (cliffordModel R).contract a

/-- Graph ↔ Clifford preservation (from general theorem). -/
theorem graph_clifford_preserves (a : R.Omega) :
    (graphModel R).contract.decode
      ((graphModel R).contract.encode
        ((cliffordModel R).contract.decode
          ((cliffordModel R).contract.encode a))) = a :=
  cross_lens_preserves R (graphModel R).contract (cliffordModel R).contract a

/-- Full cycle: Tensor → Graph → Clifford → Tensor (from general theorem). -/
theorem full_cycle_preserves (a : R.Omega) :
    (tensorModel R dim).contract.decode
      ((tensorModel R dim).contract.encode
        ((cliffordModel R).contract.decode
          ((cliffordModel R).contract.encode
            ((graphModel R).contract.decode
              ((graphModel R).contract.encode
                ((tensorModel R dim).contract.decode
                  ((tensorModel R dim).contract.encode a))))))) = a :=
  chain3_preserves R
    (tensorModel R dim).contract
    (graphModel R).contract
    (cliffordModel R).contract
    a

/-- All three lenses produce the same logical shadow. -/
theorem all_shadows_eq (a : R.Omega) :
    interiorized R (tensorModel R dim).contract ((tensorModel R dim).contract.encode a) =
    interiorized R (graphModel R).contract ((graphModel R).contract.encode a) ∧
    interiorized R (graphModel R).contract ((graphModel R).contract.encode a) =
    interiorized R (cliffordModel R).contract ((cliffordModel R).contract.encode a) :=
  ⟨logical_shadow_universal R (tensorModel R dim).contract (graphModel R).contract a,
   logical_shadow_universal R (graphModel R).contract (cliffordModel R).contract a⟩

end Instantiation

/-! ## Concrete Element Tests

These tests instantiate the general theorems with specific universal elements (⊤, ⊥)
that exist in every R.Omega. This verifies the machinery works with actual values. -/

section ConcreteElementTests

variable (dim : ℕ)

/-- **Test 1**: Top element ⊤ is preserved through Tensor↔Graph round-trip. -/
theorem top_preserved_tensor_graph :
    (tensorModel R dim).contract.decode
      ((tensorModel R dim).contract.encode
        ((graphModel R).contract.decode
          ((graphModel R).contract.encode (⊤ : R.Omega)))) = ⊤ :=
  tensor_graph_preserves R dim ⊤

/-- **Test 2**: Bottom element ⊥ is preserved through Tensor↔Graph round-trip. -/
theorem bot_preserved_tensor_graph :
    (tensorModel R dim).contract.decode
      ((tensorModel R dim).contract.encode
        ((graphModel R).contract.decode
          ((graphModel R).contract.encode (⊥ : R.Omega)))) = ⊥ :=
  tensor_graph_preserves R dim ⊥

/-- **Test 3**: Top preserved through Graph↔Clifford round-trip. -/
theorem top_preserved_graph_clifford :
    (graphModel R).contract.decode
      ((graphModel R).contract.encode
        ((cliffordModel R).contract.decode
          ((cliffordModel R).contract.encode (⊤ : R.Omega)))) = ⊤ :=
  graph_clifford_preserves R ⊤

/-- **Test 4**: Bottom preserved through Graph↔Clifford round-trip. -/
theorem bot_preserved_graph_clifford :
    (graphModel R).contract.decode
      ((graphModel R).contract.encode
        ((cliffordModel R).contract.decode
          ((cliffordModel R).contract.encode (⊥ : R.Omega)))) = ⊥ :=
  graph_clifford_preserves R ⊥

/-- **Test 5**: Full cycle Tensor→Graph→Clifford→Tensor preserves ⊤. -/
theorem top_full_cycle :
    (tensorModel R dim).contract.decode
      ((tensorModel R dim).contract.encode
        ((cliffordModel R).contract.decode
          ((cliffordModel R).contract.encode
            ((graphModel R).contract.decode
              ((graphModel R).contract.encode
                ((tensorModel R dim).contract.decode
                  ((tensorModel R dim).contract.encode (⊤ : R.Omega)))))))) = ⊤ :=
  full_cycle_preserves R dim ⊤

/-- **Test 6**: Full cycle preserves ⊥. -/
theorem bot_full_cycle :
    (tensorModel R dim).contract.decode
      ((tensorModel R dim).contract.encode
        ((cliffordModel R).contract.decode
          ((cliffordModel R).contract.encode
            ((graphModel R).contract.decode
              ((graphModel R).contract.encode
                ((tensorModel R dim).contract.decode
                  ((tensorModel R dim).contract.encode (⊥ : R.Omega)))))))) = ⊥ :=
  full_cycle_preserves R dim ⊥

/-- **Test 7**: All three lenses agree on the logical shadow of ⊤.
    This shows R(⊤) is computed the same way through any lens. -/
theorem all_shadows_agree_on_top :
    interiorized R (tensorModel R dim).contract ((tensorModel R dim).contract.encode (⊤ : R.Omega)) =
    interiorized R (graphModel R).contract ((graphModel R).contract.encode (⊤ : R.Omega)) ∧
    interiorized R (graphModel R).contract ((graphModel R).contract.encode (⊤ : R.Omega)) =
    interiorized R (cliffordModel R).contract ((cliffordModel R).contract.encode (⊤ : R.Omega)) :=
  all_shadows_eq R dim ⊤

/-- **Test 8**: All three lenses agree on the logical shadow of ⊥. -/
theorem all_shadows_agree_on_bot :
    interiorized R (tensorModel R dim).contract ((tensorModel R dim).contract.encode (⊥ : R.Omega)) =
    interiorized R (graphModel R).contract ((graphModel R).contract.encode (⊥ : R.Omega)) ∧
    interiorized R (graphModel R).contract ((graphModel R).contract.encode (⊥ : R.Omega)) =
    interiorized R (cliffordModel R).contract ((cliffordModel R).contract.encode (⊥ : R.Omega)) :=
  all_shadows_eq R dim ⊥

/-- **Test 9**: Cross-lens transformation is symmetric for any element.
    a → Tensor → Graph → a  equals  a → Graph → Tensor → a  (both equal a). -/
theorem cross_lens_symmetric (a : R.Omega) :
    (tensorModel R dim).contract.decode ((tensorModel R dim).contract.encode
      ((graphModel R).contract.decode ((graphModel R).contract.encode a))) =
    (graphModel R).contract.decode ((graphModel R).contract.encode
      ((tensorModel R dim).contract.decode ((tensorModel R dim).contract.encode a))) := by
  -- Both sides equal `a` by round-trip, hence equal to each other
  have h1 := tensor_graph_preserves R dim a
  have h2 := graph_tensor_preserves R dim a
  rw [h1, h2]

/-- **Test 10**: Multiple round-trips are idempotent (both equal a). -/
theorem double_roundtrip_idempotent (a : R.Omega) :
    let once := (tensorModel R dim).contract.decode ((tensorModel R dim).contract.encode a)
    let twice := (tensorModel R dim).contract.decode ((tensorModel R dim).contract.encode
                   ((tensorModel R dim).contract.decode ((tensorModel R dim).contract.encode a)))
    once = twice := by
  simp only [(tensorModel R dim).contract.round a]

/-- **Test 11**: Tensor round-trip on ⊤ produces ⊤. -/
theorem tensor_roundtrip_top :
    (tensorModel R dim).contract.decode ((tensorModel R dim).contract.encode (⊤ : R.Omega)) = ⊤ :=
  (tensorModel R dim).contract.round ⊤

/-- **Test 12**: Graph round-trip on ⊤ produces ⊤. -/
theorem graph_roundtrip_top :
    (graphModel R).contract.decode ((graphModel R).contract.encode (⊤ : R.Omega)) = ⊤ :=
  (graphModel R).contract.round ⊤

/-- **Test 13**: Clifford round-trip on ⊤ produces ⊤. -/
theorem clifford_roundtrip_top :
    (cliffordModel R).contract.decode ((cliffordModel R).contract.encode (⊤ : R.Omega)) = ⊤ :=
  (cliffordModel R).contract.round ⊤

end ConcreteElementTests

/-! ## Summary -/

/-
## What We Proved

### General Theorems (work for ANY lens with RoundTrip contract)

1. `cross_lens_preserves`:
   For any contracts C1, C2 over R:
   `C1.decode (C1.encode (C2.decode (C2.encode a))) = a`

2. `chain3_preserves`:
   For any contracts C1, C2, C3 over R:
   Chaining through all three preserves content

3. `logical_shadow_universal`:
   For any contracts C1, C2 over R:
   `interiorized R C1 (C1.encode a) = interiorized R C2 (C2.encode a)`

### Why This Approach Is Better

- **One proof works for all lens pairs** - no combinatorial explosion
- **New lenses automatically inherit these properties** - just provide RoundTrip contract
- **Proofs are about the interface, not implementations** - more robust
- **Mathematical essence is clear** - round-trip law is the key invariant

### The R-Nucleus Hub Architecture

```
     Any Lens ───encode───► R.Omega ───encode───► Any Other Lens
         ▲                     │                       │
         │                     │                       │
         └───────decode────────┴───────decode──────────┘
```

The `RoundTrip` contract guarantees: `decode (encode a) = a`

This single property ensures ALL cross-lens transformations preserve content.
-/

end Bridges
end Tests
end HeytingLean
