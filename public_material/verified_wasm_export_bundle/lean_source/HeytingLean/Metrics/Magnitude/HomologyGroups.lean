import HeytingLean.Metrics.Magnitude.Homology
import HeytingLean.Computational.Homology.F2Matrix
import HeytingLean.Computational.Homology.ChainComplex
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace HeytingLean
namespace Metrics
namespace Magnitude

universe u

open HeytingLean.Computational.Homology

variable {α : Type u} [Fintype α] [DecidableEq α]

instance instDecidableEqMagnitudeChain (n : Nat) : DecidableEq (MagnitudeChain α n) := by
  unfold MagnitudeChain
  infer_instance

/-- The group of `n`-cycles: `ker(d_n)` on the integer-valued chain model. -/
def magnitudeCycles (n : Nat) : Set (MagnitudeChain α (n + 1) → ℤ) :=
  { f | ∀ τ, magnitudeDifferential n f τ = 0 }

/-- The group of `n`-boundaries: `im(d_{n+1})` on the integer-valued chain model. -/
def magnitudeBoundaries (n : Nat) : Set (MagnitudeChain α (n + 1) → ℤ) :=
  { f | ∃ g : MagnitudeChain α (n + 2) → ℤ, magnitudeDifferential (n + 1) g = f }

/-- Every boundary is a cycle, by `d ∘ d = 0`. -/
theorem boundary_subset_cycles (n : Nat) :
    magnitudeBoundaries (α := α) n ⊆ magnitudeCycles (α := α) n := by
  intro f hf τ
  rcases hf with ⟨g, rfl⟩
  exact magnitudeDifferential_squared n g τ

theorem magnitudeDifferential_add (n : Nat)
    (f g : MagnitudeChain α (n + 1) → ℤ) :
    magnitudeDifferential n (fun σ => f σ + g σ) =
      fun τ => magnitudeDifferential n f τ + magnitudeDifferential n g τ := by
  funext τ
  unfold magnitudeDifferential
  simp [add_mul, Finset.sum_add_distrib]

theorem magnitudeDifferential_neg (n : Nat)
    (f : MagnitudeChain α (n + 1) → ℤ) :
    magnitudeDifferential n (fun σ => -f σ) =
      fun τ => -magnitudeDifferential n f τ := by
  funext τ
  unfold magnitudeDifferential
  simp

/-- Two chains are homologous if they differ by a boundary. -/
def sameHomologyClass (n : Nat) (f g : MagnitudeChain α (n + 1) → ℤ) : Prop :=
  ∃ b, b ∈ magnitudeBoundaries (α := α) n ∧ f = fun τ => g τ + b τ

/-- Quotient presentation of `MH_n = ker(d_n) / im(d_{n+1})` at the chain-function level. -/
def magnitudeHomologyGroup (n : Nat) : Type _ :=
  Quot (sameHomologyClass (α := α) n)

/-- Additive subgroup of cycles in degree `n`. -/
def magnitudeCyclesAddSubgroup (n : Nat) :
    AddSubgroup (MagnitudeChain α (n + 1) → ℤ) where
  carrier := magnitudeCycles (α := α) n
  zero_mem' := by
    intro τ
    simp [magnitudeDifferential]
  add_mem' := by
    intro f g hf hg
    intro τ
    have hsum := congrArg (fun h => h τ) (magnitudeDifferential_add (α := α) n f g)
    simpa [hf τ, hg τ] using hsum
  neg_mem' := by
    intro f hf
    intro τ
    have hneg := congrArg (fun h => h τ) (magnitudeDifferential_neg (α := α) n f)
    simpa [hf τ] using hneg

/-- Additive subgroup of boundaries in degree `n`. -/
def magnitudeBoundariesAddSubgroup (n : Nat) :
    AddSubgroup (MagnitudeChain α (n + 1) → ℤ) where
  carrier := magnitudeBoundaries (α := α) n
  zero_mem' := by
    refine ⟨fun _ => 0, ?_⟩
    funext τ
    simp [magnitudeDifferential]
  add_mem' := by
    intro f g hf hg
    rcases hf with ⟨f', rfl⟩
    rcases hg with ⟨g', rfl⟩
    refine ⟨fun σ => f' σ + g' σ, ?_⟩
    funext τ
    simp [magnitudeDifferential_add]
  neg_mem' := by
    intro f hf
    rcases hf with ⟨f', rfl⟩
    refine ⟨fun σ => -f' σ, ?_⟩
    funext τ
    simp [magnitudeDifferential_neg]

theorem magnitudeBoundariesAddSubgroup_le_cyclesAddSubgroup (n : Nat) :
    magnitudeBoundariesAddSubgroup (α := α) n ≤
      magnitudeCyclesAddSubgroup (α := α) n := by
  exact boundary_subset_cycles (α := α) n

/-- Boundaries as a subgroup of cycles (for the quotient-group presentation). -/
def magnitudeBoundariesInCyclesAddSubgroup (n : Nat) :
    AddSubgroup (magnitudeCyclesAddSubgroup (α := α) n) where
  carrier := {x | (x : MagnitudeChain α (n + 1) → ℤ) ∈ magnitudeBoundariesAddSubgroup (α := α) n}
  zero_mem' := by
    exact (magnitudeBoundariesAddSubgroup (α := α) n).zero_mem
  add_mem' := by
    intro x y hx hy
    exact (magnitudeBoundariesAddSubgroup (α := α) n).add_mem hx hy
  neg_mem' := by
    intro x hx
    exact (magnitudeBoundariesAddSubgroup (α := α) n).neg_mem hx

/-- Group-structured quotient model of magnitude homology:
`MH_n = Z_n / B_n` as an additive commutative group. -/
def magnitudeHomologyGroupAdd (n : Nat) : Type _ :=
  (magnitudeCyclesAddSubgroup (α := α) n) ⧸
    (magnitudeBoundariesInCyclesAddSubgroup (α := α) n)

/-- Basis delta on a finite chain set. -/
def chainDelta {n : Nat}
    (σ : MagnitudeChain α (n + 1)) : MagnitudeChain α (n + 1) → ℤ := by
  exact fun σ' => if σ' = σ then 1 else 0

/-- Coefficient parity for boundary matrices over `F₂`. -/
def boundaryCoeffMod2
    (n : Nat) (τ : MagnitudeChain α n) (σ : MagnitudeChain α (n + 1)) : Bool :=
  decide ((magnitudeDifferential n (chainDelta (α := α) σ) τ) % 2 ≠ 0)

/-- Finite basis array for degree-`n` chain generators. -/
noncomputable def chainBasis (n : Nat) : Array (MagnitudeChain α n) :=
  (Fintype.elems (α := MagnitudeChain α n)).toList.toArray

/-- Degree-`n` boundary matrix over `F₂`, with rows indexed by `C_n`,
columns by `C_{n+1}`. -/
noncomputable def boundaryMatrix (n : Nat) : F2Matrix :=
  let rowsA := chainBasis (α := α) n
  let colsA := chainBasis (α := α) (n + 1)
  { rows := rowsA.size
    cols := colsA.size
    data := Array.ofFn (fun r : Fin rowsA.size =>
      Array.ofFn (fun c : Fin colsA.size =>
        boundaryCoeffMod2 (α := α) n (rowsA[r]) (colsA[c]))) }

/-- Rank of `d_{n+1}` over `F₂` from the explicit boundary matrix. -/
noncomputable def boundaryRank (n : Nat) : Nat :=
  (boundaryMatrix (α := α) n).rank

/-- Computational Betti number (rank-nullity form) over `F₂`. -/
noncomputable def betti (β : Type u) [Fintype β] [DecidableEq β] (n : Nat) : Nat :=
  let c := chainRank β n
  let rPrev :=
    match n with
    | 0 => 0
    | m + 1 => boundaryRank (α := β) m
  let rNext := boundaryRank (α := β) n
  c - rPrev - rNext

/-- Build an `F₂` matrix from sparse "columns of ones", with a zero fallback
that is never used for well-formed hardcoded data. -/
def matrixFromColOnes (rows cols : Nat) (colOnes : Array (Array Nat)) : F2Matrix :=
  match F2Matrix.ofColOnes rows cols colOnes with
  | .ok M => M
  | .error _ => F2Matrix.zero rows cols

/-- The hardcoded `Bool` magnitude complex (degrees `0..3`) over `F₂`. -/
def boolMagnitudeComplexF2 : ChainComplexF2 where
  dims := #[2, 2, 2, 2]
  boundaries := #[
    matrixFromColOnes 2 2 #[
      #[0, 1], #[0, 1]
    ],
    matrixFromColOnes 2 2 #[
      #[0, 1], #[0, 1]
    ],
    matrixFromColOnes 2 2 #[
      #[0, 1], #[0, 1]
    ]
  ]

/-- The hardcoded `Fin 3` magnitude complex (degrees `0..3`) over `F₂`. -/
def fin3MagnitudeComplexF2 : ChainComplexF2 where
  dims := #[3, 6, 12, 24]
  boundaries := #[
    matrixFromColOnes 3 6 #[
      #[0, 1], #[0, 2], #[0, 1], #[1, 2], #[0, 2], #[1, 2]
    ],
    matrixFromColOnes 6 12 #[
      #[0, 2], #[0, 1, 3], #[1, 4], #[0, 1, 5],
      #[0, 2], #[1, 2, 3], #[2, 3, 4], #[3, 5],
      #[0, 4, 5], #[1, 4], #[2, 4, 5], #[3, 5]
    ],
    matrixFromColOnes 12 24 #[
      #[0, 4], #[0, 1, 5], #[0, 1, 2, 6], #[1, 3, 7],
      #[2, 3, 8], #[2, 9], #[0, 2, 3, 10], #[1, 3, 11],
      #[0, 4], #[1, 4, 5], #[2, 5, 6], #[3, 4, 5, 7],
      #[4, 6, 7, 8], #[5, 6, 9], #[6, 7, 10], #[7, 11],
      #[0, 8, 10], #[1, 8, 9, 11], #[2, 9], #[3, 8, 9],
      #[4, 8, 10], #[5, 9, 10, 11], #[6, 10, 11], #[7, 11]
    ]
  ]

/-- Betti extraction from an explicit finite `F₂` complex. -/
def bettiFromComplex (C : ChainComplexF2) (n : Nat) : Nat :=
  match ChainComplexF2.bettiAt C n with
  | .ok b => b
  | .error _ => 0

end Magnitude
end Metrics
end HeytingLean
