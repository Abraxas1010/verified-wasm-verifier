import HeytingLean.LoF.Bauer.DomainTheory

/-!
# Bauer: domains with basis (Phase 2 interface)

This module adds a lightweight **interface** for “countably based domains” in the
synthetic domain theory sense:

* an `OmegaCPPO` structure (ω-chain suprema + ⊥),
* a notion of ω-compact element (finite approximation),
* a countable basis (enumeration of compact elements),
* an approximation property (every element is a supremum of a compact ω-chain),
* and an optional continuity principle (recorded separately in `DomainTheory`).

We keep this *parametric* and *local* (no global axioms), mirroring the project QA contract.
-/

namespace HeytingLean
namespace LoF
namespace Bauer

universe u

open FixedPoint
open OmegaCPPO

variable {D : Type u} [PartialOrder D] [OrderBot D] [OmegaCPPO D]

/-- An element is ω-compact if it is “reached at a finite stage” of any ω-chain
whose supremum lies above it. -/
def OmegaCompact (k : D) : Prop :=
  ∀ (α : Nat → D) (hα : Monotone α), k ≤ ωSup α hα → ∃ n, k ≤ α n

/-- A **countably based domain**: an ωCPPO equipped with compact elements and a countable basis.

This is intentionally an interface (not a concrete construction). -/
structure CountablyBasedDomain (D : Type u) [PartialOrder D] [OrderBot D] [OmegaCPPO D] where
  /-- Compact elements (finite approximations). -/
  compact : D → Prop
  /-- Compactness implies ω-compactness (finite-stage witness). -/
  compact_omegaCompact : ∀ {k : D}, compact k → OmegaCompact (D := D) k
  /-- A countable basis enumerating compact elements. -/
  basis : Nat → D
  /-- Every basis element is compact. -/
  basis_compact : ∀ n, compact (basis n)
  /-- Every element is the supremum of a compact ω-chain. -/
  approx :
    ∀ x : D, ∃ α : Nat → D, ∃ hα : Monotone α, (∀ n, compact (α n)) ∧ ωSup α hα = x

namespace CountablyBasedDomain

variable {D : Type u} [PartialOrder D] [OrderBot D] [OmegaCPPO D]
variable (Dom : CountablyBasedDomain (D := D))

/-- Convenience lemma: basis elements are ω-compact. -/
lemma omegaCompact_basis (n : Nat) : OmegaCompact (D := D) (Dom.basis n) :=
  Dom.compact_omegaCompact (Dom.basis_compact n)

end CountablyBasedDomain

/-! ## Toy instance: `Set Bool` is a tiny countably based domain -/

namespace Toy

open scoped Classical

-- Work in the complete lattice of subsets; this gives `OmegaCPPO` automatically.
local instance : OmegaCPPO (Set Bool) :=
  instOmegaCPPO_ofCompleteLattice (D := Set Bool)

/-- On `Set Bool`, every element is ω-compact (finite carrier). -/
lemma omegaCompact_all (k : Set Bool) : OmegaCompact (D := Set Bool) k := by
  intro α hα hk
  -- For each boolean, if it is in k then it must appear at some stage of the chain.
  have hfalse : (false ∈ k) → ∃ n, false ∈ α n := by
    intro hf
    have : false ∈ ωSup α hα := hk hf
    have hi : false ∈ iSup α := by
      change false ∈ ωSup α hα
      exact this
    simpa using hi
  have htrue : (true ∈ k) → ∃ n, true ∈ α n := by
    intro ht
    have : true ∈ ωSup α hα := hk ht
    have hi : true ∈ iSup α := by
      change true ∈ ωSup α hα
      exact this
    simpa using hi

  -- Take a stage after both (if needed) have appeared; monotonicity then gives k ⊆ α N.
  classical
  by_cases hf : false ∈ k <;> by_cases ht : true ∈ k
  · rcases hfalse hf with ⟨n0, hn0⟩
    rcases htrue ht with ⟨n1, hn1⟩
    refine ⟨max n0 n1, ?_⟩
    intro b hb
    cases b with
    | false =>
        have : false ∈ α n0 := hn0
        exact hα (Nat.le_max_left _ _) this
    | true =>
        have : true ∈ α n1 := hn1
        exact hα (Nat.le_max_right _ _) this
  · -- false in k, true not in k
    rcases hfalse hf with ⟨n0, hn0⟩
    refine ⟨n0, ?_⟩
    intro b hb
    cases b with
    | false => exact hn0
    | true => cases (ht hb)
  · -- true in k, false not in k
    rcases htrue ht with ⟨n1, hn1⟩
    refine ⟨n1, ?_⟩
    intro b hb
    cases b with
    | true => exact hn1
    | false => cases (hf hb)
  · -- k is empty
    refine ⟨0, ?_⟩
    intro b hb
    cases b with
    | false => exact (hf hb).elim
    | true => exact (ht hb).elim

/-- A tiny basis enumerating the four subsets of `Bool`. -/
def basis : Nat → Set Bool
  | 0 => (∅ : Set Bool)
  | 1 => {false}
  | 2 => {true}
  | _ => (⊤ : Set Bool)

/-- `Set Bool` as a countably based domain (all elements compact; trivial approximation). -/
def domain : CountablyBasedDomain (D := Set Bool) where
  compact := fun _ => True
  compact_omegaCompact := by
    intro k _
    exact omegaCompact_all k
  basis := basis
  basis_compact := by intro n; exact trivial
  approx := by
    intro x
    refine ⟨fun _ => x, ?_, ?_, ?_⟩
    · intro a b hab
      -- constant chain
      simp
    · intro n
      exact trivial
    · -- ωSup of constant chain is x
      -- `x` is both an upper bound and a member of the chain.
      apply le_antisymm
      · apply OmegaCPPO.ωSup_le
        intro n
        exact le_rfl
      · simpa using (OmegaCPPO.le_ωSup (D := Set Bool) (α := fun _ => x) (hα := by
          intro a b hab; exact le_rfl) 0)

end Toy

end Bauer
end LoF
end HeytingLean
