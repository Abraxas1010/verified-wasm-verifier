import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-
# Emergence Selector — core types

This module introduces the core finite-state types used by the
Emergence Selector:

* a transition probability matrix `TPM n` on `Fin n`, and
* a simple `Partition n` of the finite state space.

Later phases layer causal primitives (determinism, degeneracy, CP) and
partition-lattice structure on top of these types.
-/

namespace HeytingLean
namespace Bridges
namespace Emergence

open scoped ENNReal

/-- Sum the elements of a list of real numbers. -/
noncomputable def sumListReal (xs : List ℝ) : ℝ :=
  xs.foldl (fun acc x => acc + x) 0

/-- A finite-state transition probability matrix on `Fin n`.

The entry `prob i j` is the probability of transitioning from state
`i` to state `j`. The `row_stochastic` field records a normalisation
property for the rows (for example, that each row forms a probability
distribution); concrete instances can choose the precise predicate
appropriate for their setting. -/
structure TPM (n : Nat) where
  prob : Fin n → Fin n → ℝ≥0∞
  row_stochastic : Prop

/-- A partition of the finite state space `Fin n` into blocks.

The `blocks` field lists the blocks as lists of indices. Subsequent
phases will add utilities and, where helpful, additional structure on
top of this representation for refinement and hierarchy calculations.
-/
structure Partition (n : Nat) where
  blocks : List (List (Fin n))
deriving Repr

/-- Sum the elements of a list of `ℝ≥0∞`. This is a small, local helper
used to define coarse-grained transition probabilities without relying
on big-operator notation. -/
noncomputable def sumList (xs : List ℝ≥0∞) : ℝ≥0∞ :=
  xs.foldl (fun acc x => acc + x) 0

namespace Partition

variable {n : Nat}

/-- Extract the `i`‑th block (as a list of states) from a `Partition n`,
using the canonical index carried by `Fin`. -/
def blockOf (π : Partition n) (i : Fin π.blocks.length) : List (Fin n) :=
  π.blocks.get ⟨i.1, i.2⟩

end Partition

/-- Refinement relation between two partitions on the same state space.

`refines π₁ π₂` means: every block of `π₁` is contained in some block
of `π₂`. This is the natural partial order on partitions used to build
emergent hierarchies. -/
def refines {n : Nat} (π₁ π₂ : Partition n) : Prop :=
  ∀ b ∈ π₁.blocks,
    ∃ b₂ ∈ π₂.blocks, ∀ i : Fin n, i ∈ b → i ∈ b₂

@[refl]
lemma refines_refl {n : Nat} (π : Partition n) : refines π π := by
  intro b hb
  refine ⟨b, hb, ?_⟩
  intro i hi
  exact hi

@[trans]
lemma refines_trans {n : Nat} {π₁ π₂ π₃ : Partition n}
    (h₁₂ : refines π₁ π₂) (h₂₃ : refines π₂ π₃) :
    refines π₁ π₃ := by
  intro b hb
  rcases h₁₂ b hb with ⟨b₂, hb₂, hsub₁₂⟩
  rcases h₂₃ b₂ hb₂ with ⟨b₃, hb₃, hsub₂₃⟩
  refine ⟨b₃, hb₃, ?_⟩
  intro i hi
  exact hsub₂₃ i (hsub₁₂ i hi)

/-- Coarse-grain a microscale TPM along a given partition.

Each macro-state corresponds to a block of micro-states. For now we
define the macro transition probability from block `i` to block `j`
as the average over micro-states in `i` of the total probability to
land in any micro-state in `j`, using the uniform measure on the
source block. -/
noncomputable def TPM.coarseGrain {n : Nat} (P : TPM n) (π : Partition n) :
    TPM π.blocks.length :=
  let prob' (i j : Fin π.blocks.length) : ℝ≥0∞ :=
    let Bi := Partition.blockOf π i
    let Bj := Partition.blockOf π j
    let inner (s : Fin n) : ℝ≥0∞ :=
      sumList (Bj.map (fun t => P.prob s t))
    let total : ℝ≥0∞ := sumList (Bi.map inner)
    let denom : ℝ≥0∞ := (Bi.length : ℝ≥0∞)
    -- Guard the empty-block case explicitly; in that degenerate case
    -- we return 0 rather than dividing by 0.
    if Bi.length = 0 then
      0
    else
      total / denom
  { prob := prob'
    -- We carry over the normalisation flag from the microscale TPM.
    -- Later phases can refine this to a concrete row-sum property for
    -- the coarse-grained matrix when required.
    row_stochastic := P.row_stochastic }

/-! ## Causal primitives: determinism, degeneracy, CP

The following noncomputable definitions implement the information-
theoretic primitives from causal emergence theory for finite TPMs.
They are intended for specification, analysis, and reporting; they
are not used on performance-critical runtime paths.
-/

noncomputable section

/-- Base-2 logarithm on reals. This is a thin wrapper around the
natural logarithm used to keep formulas close to the paper. -/
def log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

/-- Entropy (in bits) of a finite real-valued probability vector
represented as a list. Zero-mass entries contribute `0`. -/
def entropyList (ps : List ℝ) : ℝ :=
  ps.foldl
    (fun acc p =>
      if p = 0 then
        acc
      else
        acc - p * log2 p)
    0

/-- Row-wise conditional entropy `H(E ∣ C)` in bits, assuming a
uniform prior over causes. For each cause state `i`, we form the
list of `P(e ∣ i)` values over all effects `e : Fin n`, convert to
reals, take the Shannon entropy, and average across `i`. -/
def condEntropy (P : TPM n) : ℝ :=
  let states : List (Fin n) := List.finRange n
  let rowEntropies : List ℝ :=
    states.map (fun i =>
      let row : List ℝ := states.map (fun j => (P.prob i j).toReal)
      entropyList row)
  let total := sumListReal rowEntropies
  if n = 0 then
    0
  else
    total / (n : ℝ)

/-- Entropy of the marginal effect distribution `P(E)` in bits, under
a uniform prior on causes. -/
def effectEntropy (P : TPM n) : ℝ :=
  let states : List (Fin n) := List.finRange n
  -- marginal `P(e)` for each effect `e`, assuming uniform causes
  let pe : List ℝ :=
    states.map (fun e =>
      if n = 0 then
        0
      else
        let weights : List ℝ :=
          states.map (fun c => (P.prob c e).toReal)
        let total := sumListReal weights
        total / (n : ℝ))
  entropyList pe

/-- Determinism of a finite TPM, following the CE 2.0 / Engineering
Emergence definition

`determinism = 1 - H(E ∣ C) / log₂ n`,

where `n` is the number of effect states and `H(E ∣ C)` is the
row-wise conditional entropy in bits under a uniform prior on
causes. For degenerate systems with `n ≤ 1` we set determinism to 1. -/
def determinism (P : TPM n) : ℝ :=
  if n ≤ 1 then
    1
  else
    let nR : ℝ := n
    let logN := log2 nR
    1 - condEntropy P / logN

/-- Degeneracy of a finite TPM, based on the entropy of the marginal
effect distribution `P(E)`:

`degeneracy = 1 - H(E) / log₂ n`,

where `H(E)` is measured in bits and `n` is the number of effect
states. For degenerate systems with `n ≤ 1` we set degeneracy to 0. -/
def degeneracy (P : TPM n) : ℝ :=
  if n ≤ 1 then
    0
  else
    let nR : ℝ := n
    let logN := log2 nR
    1 - effectEntropy P / logN

/-- Specificity, defined as `1 - degeneracy`. -/
def specificity (P : TPM n) : ℝ :=
  1 - degeneracy P

/- Causal power `CP` of a finite TPM, in the CE 2.0 / Engineering
Emergence sense:

`CP = determinism + specificity - 1`. -/
def CP (P : TPM n) : ℝ :=
  determinism P + specificity P - 1

/-- Microscale causal power is just `CP` of the original TPM. -/
def CP_micro (P : TPM n) : ℝ :=
  CP P

/-- Macroscale causal power at a partition `π`, defined as the causal
power of the coarse-grained TPM. -/
def CP_macro (P : TPM n) (π : Partition n) : ℝ :=
  CP (P.coarseGrain π)

/-- ΔCP at a partition `π` relative to a finite candidate set of
partitions. We subtract the maximum macroscale CP of any *proper*
refinement of `π` appearing in the candidate list. This mirrors the
causal emergence "apportionment" rule on a finite lattice. -/
def deltaCPOver (P : TPM n) (π : Partition n) (candidates : List (Partition n)) :
    ℝ :=
  let base := CP_macro P π
  let supPred :=
    candidates.foldl
      (fun acc π' =>
        match Classical.dec (refines π' π ∧ π' ≠ π) with
        | isTrue _  => max acc (CP_macro P π')
        | isFalse _ => acc)
      0
  base - supPred

/-- Helper: list of nonnegative ΔCP values for each partition in a
candidate set. Negative contributions are clamped to `0` to reflect
the "non-redundant" contributors in the emergent hierarchy. -/
def deltaCPList (P : TPM n) (candidates : List (Partition n)) :
    List (Partition n × ℝ) :=
  candidates.map (fun π =>
    let δ := deltaCPOver P π candidates
    (π, max 0 δ))

/-- The emergent hierarchy for a TPM relative to a finite candidate
set of partitions: those partitions with strictly positive ΔCP. -/
def emergentHierarchy (P : TPM n) (candidates : List (Partition n)) :
    List (Partition n) :=
  candidates.filter (fun π => deltaCPOver P π candidates > 0)

/-- A simple scale index for a partition: the number of blocks. This
is monotone under refinement and gives a natural "level" coordinate
for ΔCP mass. -/
def levelOf {n : Nat} (π : Partition n) : Nat :=
  π.blocks.length

/-- Update the accumulated ΔCP mass for a given level. If the level is
already present, we add to its mass; otherwise we insert a new entry. -/
def updateLevelMass (lvl : Nat) (δ : ℝ) (xs : List (Nat × ℝ)) :
    List (Nat × ℝ) :=
  match xs with
  | [] => [(lvl, δ)]
  | (ℓ, m) :: rest =>
      if ℓ = lvl then
        (ℓ, m + δ) :: rest
      else
        (ℓ, m) :: updateLevelMass lvl δ rest

/-- Aggregate ΔCP mass per level (as measured by `levelOf`) for a
finite candidate set of partitions. Levels with zero total ΔCP are
omitted. -/
def levelMasses (P : TPM n) (candidates : List (Partition n)) :
    List (Nat × ℝ) :=
  let deltas := deltaCPList P candidates
  deltas.foldl
    (fun acc pr =>
      let π := pr.1
      let δ := pr.2
      if δ = 0 then
        acc
      else
        updateLevelMass (levelOf π) δ acc)
    []

/-- Path-spread complexity `S_path` for a finite candidate set of
partitions: the Shannon entropy (in bits) of the normalised ΔCP
distribution over individual partitions. When the total ΔCP mass is
zero, we return `0`. -/
def S_path (P : TPM n) (candidates : List (Partition n)) : ℝ :=
  let deltas := deltaCPList P candidates
  let vals : List ℝ := deltas.map (fun pr => pr.2)
  let total := sumListReal vals
  if total = 0 then
    0
  else
    let probs : List ℝ := vals.map (fun δ => δ / total)
    entropyList probs

/-- Row-spread complexity `S_row` for a finite candidate set of
partitions: the Shannon entropy (in bits) of the normalised ΔCP
distribution across levels, where levels are grouped by block-count.
When the total ΔCP mass is zero, we return `0`. -/
def S_row (P : TPM n) (candidates : List (Partition n)) : ℝ :=
  let masses := levelMasses P candidates
  let vals : List ℝ := masses.map (fun pr => pr.2)
  let total := sumListReal vals
  if total = 0 then
    0
  else
    let probs : List ℝ := vals.map (fun m => m / total)
    entropyList probs

/-- Qualitative regime classification for ΔCP mass distribution across
levels, mirroring the "bottom-heavy", "top-heavy", "mesoscale", and
"scale-free-like" taxonomy from the Engineering Emergence paper. -/
inductive EmergenceRegime
  | BottomHeavy
  | TopHeavy
  | Mesoscale
  | ScaleFreeLike
deriving Repr, DecidableEq

/-- Classify a finite ΔCP profile into one of the qualitative regimes:

* `BottomHeavy` if the dominant level is the finest (smallest level)
  and there is at least one strictly coarser level present;
* `TopHeavy` if the dominant level is the coarsest (largest level)
  and there is at least one strictly finer level present;
* `Mesoscale` if the dominant level lies strictly between the finest
  and coarsest levels;
* `ScaleFreeLike` in all other cases (including degenerate profiles).
-/
def classifyRegime (P : TPM n) (candidates : List (Partition n)) :
    EmergenceRegime :=
  match levelMasses P candidates with
  | [] => EmergenceRegime.ScaleFreeLike
  | (ℓ0, m0) :: rest =>
      let (bestLvl, _) :=
        rest.foldl
          (fun (acc : Nat × ℝ) lr =>
            let (_, mbest) := acc
            let (ℓ, m) := lr
            if m > mbest then
              (ℓ, m)
            else
              acc)
          (ℓ0, m0)
      let (minLvl, maxLvl) :=
        rest.foldl
          (fun (acc : Nat × Nat) lr =>
            let (mn, mx) := acc
            let (ℓ, _) := lr
            (Nat.min mn ℓ, Nat.max mx ℓ))
          (ℓ0, ℓ0)
      if bestLvl = minLvl ∧ minLvl ≠ maxLvl then
        EmergenceRegime.BottomHeavy
      else if bestLvl = maxLvl ∧ minLvl ≠ maxLvl then
        EmergenceRegime.TopHeavy
      else if minLvl < bestLvl ∧ bestLvl < maxLvl then
        EmergenceRegime.Mesoscale
      else
        EmergenceRegime.ScaleFreeLike

/-! ## Emergence pre-lens: choices and default candidates -/

/-- Default candidate partitions for a given state-space size `n`.

For now we consider a simple refinement chain consisting of the
discrete partition and the indiscrete partition. This provides a
minimal but honest spectrum of scales for the Emergence Selector; more
refined candidate families can be supplied explicitly to
`chooseScaleExact`. -/
noncomputable def defaultCandidates (n : Nat) : List (Partition n) :=
  let states : List (Fin n) := List.finRange n
  let discreteBlocks : List (List (Fin n)) :=
    states.map (fun i => [i])
  let indiscreteBlocks : List (List (Fin n)) := [states]
  [{ blocks := discreteBlocks }, { blocks := indiscreteBlocks }]

/-- Summary of an emergence-based scale choice for a fixed TPM. -/
structure EmergentChoice (n : Nat) where
  microTPM   : TPM n
  candidates : List (Partition n)
  chosen     : Partition n
  altScales  : List (Partition n)
  deltaCP_chosen : ℝ
  regime     : EmergenceRegime
  S_path     : ℝ
  S_row      : ℝ

/-- Exact Emergence Selector on a finite candidate set of partitions.

Given a microscale TPM and a nonempty list of candidate partitions, we
select a partition maximizing ΔCP, compute its complexity profile, and
record the remaining non-dominated scales as alternatives. -/
noncomputable def chooseScaleExact {n : Nat}
    (P : TPM n) (candidates : List (Partition n)) (h : candidates ≠ []) :
    EmergentChoice n := by
  classical
  -- Find an argmax of ΔCP over the candidate set.
  match candidates with
  | [] =>
      cases h rfl
  | π0 :: rest =>
      let δ0 := deltaCPOver P π0 candidates
      let (bestπ, bestδ) :=
        rest.foldl
          (fun (acc : Partition n × ℝ) π' =>
            let δ' := deltaCPOver P π' candidates
            if δ' > acc.2 then
              (π', δ')
            else
              acc)
          (π0, δ0)
      let hierarchy := emergentHierarchy P candidates
      let alt := hierarchy.filter (fun π => π ≠ bestπ)
      let Sp := S_path P candidates
      let Sr := S_row P candidates
      let reg := classifyRegime P candidates
      exact
        { microTPM := P
          candidates := candidates
          chosen := bestπ
          altScales := alt
          deltaCP_chosen := bestδ
          regime := reg
          S_path := Sp
          S_row := Sr }

/-- Default Emergence Selector using a simple refinement chain of
candidate partitions (`defaultCandidates`). This is suitable for small
systems and examples; more elaborate candidate families can be passed
directly to `chooseScaleExact`. -/
noncomputable def chooseScale {n : Nat} (P : TPM n) : EmergentChoice n :=
  let candidates := defaultCandidates n
  match candidates with
  | [] =>
      -- This branch is unreachable given the current `defaultCandidates`,
      -- but we still provide a total definition for completeness.
      { microTPM := P
        candidates := []
        chosen := { blocks := [] }
        altScales := []
        deltaCP_chosen := 0
        regime := EmergenceRegime.ScaleFreeLike
        S_path := 0
        S_row := 0 }
  | π0 :: rest =>
      let cands := π0 :: rest
      have h' : cands ≠ [] := by
        simp [cands]
      chooseScaleExact P cands h'

end

end Emergence
end Bridges
end HeytingLean
