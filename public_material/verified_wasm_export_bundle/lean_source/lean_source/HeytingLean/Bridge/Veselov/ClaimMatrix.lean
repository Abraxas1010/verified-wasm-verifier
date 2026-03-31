import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic

/-!
# Bridge.Veselov.ClaimMatrix

Claim-classification surface for Vladimir/Veselov bridge statements.
This file keeps implementation/assumption/empirical/open tags explicit.
-/

namespace HeytingLean.Bridge.Veselov

/-- Machine-readable claim status tags used for PM crosswalk artifacts. -/
inductive ClaimStatus
  | implemented
  | assumption
  | empirical
  | open
  deriving DecidableEq, Repr

/-- One claim entry with explicit source/provenance metadata. -/
structure ClaimEntry where
  id : String
  status : ClaimStatus
  sourceUrl : String
  note : String

/-- Only fully implemented claims are promotable into theorem-facing summaries. -/
def claimPromotable (c : ClaimEntry) : Prop :=
  c.status = ClaimStatus.implemented

@[simp] theorem empirical_not_promotable (c : ClaimEntry)
    (h : c.status = ClaimStatus.empirical) :
    ¬ claimPromotable c := by
  intro hp
  dsimp [claimPromotable] at hp
  simp [h] at hp

@[simp] theorem open_not_promotable (c : ClaimEntry)
    (h : c.status = ClaimStatus.open) :
    ¬ claimPromotable c := by
  intro hp
  dsimp [claimPromotable] at hp
  simp [h] at hp

/-- Small canonical matrix used by tests and reporting scripts. -/
def canonicalClaimMatrix : List ClaimEntry :=
  [ { id := "neural_universe_curvature_regime"
      status := ClaimStatus.implemented
      sourceUrl := "https://arxiv.org/abs/2210.12048"
      note := "Curvature sign-to-regime bridge has formal implementation." }
  , { id := "novikov_cover_emergent_time"
      status := ClaimStatus.assumption
      sourceUrl := "https://eudml.org/doc/138746"
      note := "Assumption-first contract; no full physical derivation in repo." }
  , { id := "asic_early_abort_gain"
      status := ClaimStatus.empirical
      sourceUrl := "https://arxiv.org/abs/2601.01916"
      note := "Numbers remain artifact-side and require provenance." }
  , { id := "sieve_prough_runtime_gain"
      status := ClaimStatus.open
      sourceUrl := "https://arxiv.org/abs/2407.14368"
      note := "No unparameterized theorem claim; tracked as open." } ]

/-- Hybrid-Zeckendorf claim slice (B1-B13 from PM inventory). -/
def hybridZeckendorfClaimMatrix : List ClaimEntry :=
  [ { id := "B1_weight_system"
      status := ClaimStatus.implemented
      sourceUrl := "https://arxiv.org/abs/2602.17533"
      note := "Weight recurrence and closed form implemented." }
  , { id := "B2_hybrid_number_type"
      status := ClaimStatus.implemented
      sourceUrl := "https://arxiv.org/abs/2602.17533"
      note := "Finite-support hybrid and lazy carriers implemented." }
  , { id := "B3_hybrid_value_formula"
      status := ClaimStatus.implemented
      sourceUrl := "https://arxiv.org/abs/2602.17533"
      note := "Evaluation semantics proved for constructors." }
  , { id := "B4_fibonacci_doubling_identity"
      status := ClaimStatus.implemented
      sourceUrl := "https://arxiv.org/abs/2602.17533"
      note := "Identity `2*F_(k+2)=F_(k+3)+F_k` proved from recurrence." }
  , { id := "B5_lazy_state_type"
      status := ClaimStatus.implemented
      sourceUrl := "https://arxiv.org/abs/2602.17533"
      note := "Lazy payload type and level evaluator implemented." }
  , { id := "B6_intra_level_normalization"
      status := ClaimStatus.implemented
      sourceUrl := "https://arxiv.org/abs/2602.17533"
      note := "Head-rewrite intra-step (duplicate/consecutive) + bounded iteration; value preservation proved." }
  , { id := "B7_inter_level_carry"
      status := ClaimStatus.implemented
      sourceUrl := "https://arxiv.org/abs/2602.17533"
      note := "Bottom-up Euclidean div/mod carry pass over finite support depth; eval and canonicality preservation proved." }
  , { id := "B8_two_stage_normalization"
      status := ClaimStatus.implemented
      sourceUrl := "https://arxiv.org/abs/2602.17533"
      note := "Levelwise intra-normalization + inter-pass composition; soundness and canonicality witness proved." }
  , { id := "B9_addition_correctness"
      status := ClaimStatus.implemented
      sourceUrl := "https://arxiv.org/abs/2602.17533"
      note := "Per-level lazy merge (payload append) with correctness theorem proved." }
  , { id := "B10_multiplication_correctness"
      status := ClaimStatus.implemented
      sourceUrl := "https://arxiv.org/abs/2602.17533"
      note := "Support-depth-bounded level fold (with per-level repeatAdd multiplicities) correctness theorem proved." }
  , { id := "B11_density_measure"
      status := ClaimStatus.implemented
      sourceUrl := "https://arxiv.org/abs/2602.17533"
      note := "Density statistic definition implemented." }
  , { id := "B12_normalization_termination"
      status := ClaimStatus.implemented
      sourceUrl := "https://arxiv.org/abs/2602.17533"
      note := "Bounded-iteration and witness-style termination lemmas provided for normalization stages." }
  , { id := "B13_canonical_uniqueness"
      status := ClaimStatus.open
      sourceUrl := "https://arxiv.org/abs/2602.17533"
      note := "Canonical uniqueness promoted to dedicated follow-up proof track." } ]

theorem hybridZeckendorfClaimMatrix_sources_nonempty :
    ∀ c ∈ hybridZeckendorfClaimMatrix, c.sourceUrl ≠ "" := by
  intro c hc
  simp [hybridZeckendorfClaimMatrix] at hc
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
  · simp [hc]
  · simp [hc]
  · simp [hc]
  · simp [hc]
  · simp [hc]
  · simp [hc]
  · simp [hc]
  · simp [hc]
  · simp [hc]
  · simp [hc]
  · simp [hc]
  · simp [hc]
  · simp [hc]

/-- Every matrix row must carry a non-empty source URL. -/
theorem canonicalClaimMatrix_sources_nonempty :
    ∀ c ∈ canonicalClaimMatrix, c.sourceUrl ≠ "" := by
  intro c hc
  simp [canonicalClaimMatrix] at hc
  rcases hc with hc | hc | hc | hc
  · simp [hc]
  · simp [hc]
  · simp [hc]
  · simp [hc]

end HeytingLean.Bridge.Veselov
