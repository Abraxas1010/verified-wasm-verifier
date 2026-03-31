import HeytingLean.Bridges.Emergence
import HeytingLean.Occam.Emergence

/-
Compliance tests for the Emergence Selector core types and causal
primitives. We keep the numeric examples tiny so that the information-
theoretic quantities remain easy to reason about in later phases.
-/

namespace HeytingLean
namespace Tests
namespace ComplianceEmergence

open Bridges.Emergence

/-- A trivial one-state TPM, useful as a sanity check that the core
structures can be instantiated without additional assumptions. -/
def tpmSingleton : TPM 1 where
  prob _ _ := 1
  row_stochastic := True

/-- The indiscrete partition on a singleton state space. -/
def partitionSingleton : Partition 1 where
  blocks := [[⟨0, by decide⟩]]

/-- Coarse-graining the singleton TPM along the unique partition yields
another one-state TPM. This example checks that `coarseGrain` is
well-typed and behaves sensibly in the simplest case. -/
noncomputable def tpmSingletonCoarse : TPM 1 :=
  (tpmSingleton).coarseGrain partitionSingleton

/-- A simple refinement example on a three-state space: the discrete
partition refines the partition which merges the last two states. -/
def partitionDiscrete3 : Partition 3 where
  blocks := [[⟨0, by decide⟩], [⟨1, by decide⟩], [⟨2, by decide⟩]]

def partitionMerge23 : Partition 3 where
  blocks := [[⟨0, by decide⟩], [⟨1, by decide⟩, ⟨2, by decide⟩]]

lemma refines_discrete_merge23 :
    refines partitionDiscrete3 partitionMerge23 := by
  intro b hb
  -- There are three possible singleton blocks in `partitionDiscrete3`.
  have h_cases :
      b = [⟨0, by decide⟩] ∨
      b = [⟨1, by decide⟩] ∨
      b = [⟨2, by decide⟩] := by
    -- Since the partition is explicitly given as these three blocks,
    -- membership forces one of the three equalities.
    simp [partitionDiscrete3] at hb
    simpa using hb
  rcases h_cases with h0 | h12
  · subst h0
    refine ⟨[⟨0, by decide⟩], ?_, ?_⟩
    · simp [partitionMerge23]
    · intro i hi
      -- Only `i = 0` can occur in this singleton block.
      simp at hi
      simp [partitionMerge23, hi]
  · rcases h12 with h1 | h2
    · subst h1
      refine ⟨[⟨1, by decide⟩, ⟨2, by decide⟩], ?_, ?_⟩
      · simp [partitionMerge23]
      · intro i hi
        simp [partitionMerge23] at hi ⊢
        exact Or.inl hi
    · subst h2
      refine ⟨[⟨1, by decide⟩, ⟨2, by decide⟩], ?_, ?_⟩
      · simp [partitionMerge23]
      · intro i hi
        simp [partitionMerge23] at hi ⊢
        exact Or.inr hi

/-- A simple two-state "copy" TPM where each state deterministically
transitions to itself. This is a convenient example where we expect
high determinism and low degeneracy. -/
def tpmCopy2 : TPM 2 where
  prob i j := if i = j then 1 else 0
  row_stochastic := True

/-- The discrete partition on two states, used as a trivial macroscale
for testing `CP_micro` and `CP_macro`. -/
def partitionDiscrete2 : Partition 2 where
  blocks := [[⟨0, by decide⟩], [⟨1, by decide⟩]]

/-- Causal power at the microscale for the copy TPM. We do not assert
any inequalities here; the goal is to ensure that the definition is
usable on concrete finite examples. -/
noncomputable def CP_copy2_micro : ℝ :=
  CP_micro tpmCopy2

/-- Causal power at the macroscale for the copy TPM under the discrete
partition. For this partition, `CP_macro` coincides with `CP_micro`. -/
noncomputable def CP_copy2_macro : ℝ :=
  CP_macro tpmCopy2 partitionDiscrete2

/-- A three-state "copy" TPM mirroring `tpmCopy2` but on `Fin 3`. -/
def tpmCopy3 : TPM 3 where
  prob i j := if i = j then 1 else 0
  row_stochastic := True

/-- The indiscrete partition on three states (single macro-state). -/
def partitionIndiscrete3 : Partition 3 where
  blocks := [[⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]]

/-- A small candidate set of partitions on three states, ordered from
finest to coarsest. -/
def candidates3 : List (Partition 3) :=
  [partitionDiscrete3, partitionMerge23, partitionIndiscrete3]

/-- ΔCP for the discrete partition in the three-state example. -/
noncomputable def deltaCP_discrete3 : ℝ :=
  deltaCPOver tpmCopy3 partitionDiscrete3 candidates3

/-- ΔCP for the merged partition in the three-state example. -/
noncomputable def deltaCP_merge23 : ℝ :=
  deltaCPOver tpmCopy3 partitionMerge23 candidates3

/-- ΔCP for the indiscrete partition in the three-state example. -/
noncomputable def deltaCP_indiscrete3 : ℝ :=
  deltaCPOver tpmCopy3 partitionIndiscrete3 candidates3

/-- Aggregated ΔCP complexity across partitions (path-spread) for the
three-state example. -/
noncomputable def S_path_copy3 : ℝ :=
  S_path tpmCopy3 candidates3

/-- Aggregated ΔCP complexity across levels (row-spread) for the
three-state example. -/
noncomputable def S_row_copy3 : ℝ :=
  S_row tpmCopy3 candidates3

/-- Qualitative regime classification for the three-state copy TPM. -/
noncomputable def regime_copy3 : EmergenceRegime :=
  classifyRegime tpmCopy3 candidates3

/-- Occam-style model complexity on partitions for the three-state
example, using the emergence-driven `ModelComplexity` profile. -/
noncomputable def complexity_copy3 :
    HeytingLean.Meta.AIT.ModelComplexity (Partition 3) :=
  HeytingLean.Occam.Emergence.emergenceModelComplexity tpmCopy3 candidates3

/-- Example of PSR robustness at the chosen macroscale under the
identity perturbation relation. This witnesses the shape of
`PSR_RobustAtScale` in a concrete tiny system. -/
noncomputable def psrRobust_copy3_chosen (ec : EmergentChoice 3) :
    HeytingLean.Occam.Emergence.PSR_RobustAtScale
      HeytingLean.Occam.Emergence.PerturbId
      ec.microTPM ec.chosen :=
  HeytingLean.Occam.Emergence.PSR_RobustAtScale_id ec.microTPM ec.chosen

/-- Dimension choice for the three-state example, driven by the
emergence regime. -/
noncomputable def dimension_copy3 (ec : EmergentChoice 3) :
    HeytingLean.Occam.Emergence.LogicDimension :=
  HeytingLean.Occam.Emergence.chooseDimension ec

end ComplianceEmergence
end Tests
end HeytingLean
