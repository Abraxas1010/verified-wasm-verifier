import HeytingLean.Metrics.Magnitude.HomologyGroups
import HeytingLean.Metrics.Magnitude.Diagonality
import HeytingLean.Metrics.Magnitude.Weighting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases

namespace HeytingLean
namespace Metrics
namespace Magnitude

universe u

open Finset

variable {α : Type u} [MetricMagnitudeSpace α]

/-- Blurred magnitude chains at threshold `t`: degree-`n` chains with total length at most `t`. -/
def BlurredChain (n t : Nat) : Type u :=
  { τ : MagnitudeChain α n // chainLength τ ≤ t }

instance instFintypeBlurredChain (n t : Nat) : Fintype (BlurredChain (α := α) n t) := by
  classical
  unfold BlurredChain
  infer_instance

/-- Inclusion map for blurred chains as threshold increases. -/
def blurredInclusion (n : Nat) {s t : Nat} (hst : s ≤ t) :
    BlurredChain (α := α) n s → BlurredChain (α := α) n t
  | ⟨τ, hτ⟩ => ⟨τ, le_trans hτ hst⟩

theorem blurredInclusion_refl (n t : Nat) :
    blurredInclusion (α := α) n (Nat.le_refl t) = id := by
  funext x
  cases x
  rfl

theorem blurredInclusion_trans (n : Nat) {r s t : Nat} (hrs : r ≤ s) (hst : s ≤ t) :
    blurredInclusion (α := α) n (le_trans hrs hst) =
      (blurredInclusion (α := α) n hst) ∘ (blurredInclusion (α := α) n hrs) := by
  funext x
  cases x
  rfl

/-- Restrict the magnitude differential to blurred codomain chains. -/
def blurredDifferentialRaw (n t : Nat)
    (f : MagnitudeChain α (n + 1) → ℤ) :
    BlurredChain (α := α) n t → ℤ :=
  fun τ => magnitudeDifferential n f τ.1

/-- The blurred raw differential still satisfies `d² = 0`, inherited from the full complex. -/
theorem blurredDifferentialRaw_squared (n t : Nat)
    (f : MagnitudeChain α (n + 2) → ℤ)
    (τ : BlurredChain (α := α) n t) :
    blurredDifferentialRaw (α := α) n t (magnitudeDifferential (n + 1) f) τ = 0 := by
  exact magnitudeDifferential_squared n f τ.1

/-- Extend a blurred cochain to all chains by zero outside the threshold. -/
def extendBlurred (n t : Nat)
    (f : BlurredChain (α := α) n t → ℤ) :
    MagnitudeChain α n → ℤ :=
  fun σ => if hσ : chainLength σ ≤ t then f ⟨σ, hσ⟩ else 0

/-- Global-support condition: a cochain vanishes on every chain above threshold `t`. -/
def ZeroAbove (n t : Nat) (g : MagnitudeChain α n → ℤ) : Prop :=
  ∀ σ : MagnitudeChain α n, t < chainLength σ → g σ = 0

/-- Extending the restricted map `σ ↦ g σ` recovers `g` when `g` is zero above `t`. -/
theorem extendBlurred_eq_of_zeroAbove (n t : Nat)
    (g : MagnitudeChain α n → ℤ)
    (hzero : ZeroAbove (α := α) n t g) :
    extendBlurred (α := α) (n := n) (t := t) (fun τ => g τ.1) = g := by
  funext σ
  by_cases hσt : chainLength σ ≤ t
  · simp [extendBlurred, hσt]
  · have hs : t < chainLength σ := lt_of_not_ge hσt
    have hz : g σ = 0 := hzero σ hs
    simp [extendBlurred, hσt, hz]

/-- Blurred differential on threshold-limited cochains (via zero extension). -/
def blurredDifferential (n t : Nat)
    (f : BlurredChain (α := α) (n + 1) t → ℤ) :
    BlurredChain (α := α) n t → ℤ :=
  blurredDifferentialRaw (α := α) n t (extendBlurred (α := α) (n := n + 1) (t := t) f)

/-- The blurred differential squares to zero once the intermediate global differential
is known to stay supported inside the threshold. -/
theorem blurredDifferential_squared (n t : Nat)
    (f : BlurredChain (α := α) (n + 2) t → ℤ)
    (hzero :
      ZeroAbove (α := α) (n := n + 1) t
        (magnitudeDifferential (n + 1)
          (extendBlurred (α := α) (n := n + 2) (t := t) f)))
    (τ : BlurredChain (α := α) n t) :
    blurredDifferential (α := α) n t
      (blurredDifferential (α := α) (n + 1) t f) τ = 0 := by
  let g : MagnitudeChain α (n + 1) → ℤ :=
    magnitudeDifferential (n + 1)
      (extendBlurred (α := α) (n := n + 2) (t := t) f)
  have hext :
      extendBlurred (α := α) (n := n + 1) (t := t)
        (blurredDifferential (α := α) (n + 1) t f) = g := by
    have hzero' : ZeroAbove (α := α) (n := n + 1) t g := by
      simpa [g] using hzero
    simpa [g, blurredDifferential, blurredDifferentialRaw] using
      (extendBlurred_eq_of_zeroAbove (α := α) (n := n + 1) (t := t) g hzero')
  calc
    blurredDifferential (α := α) n t
        (blurredDifferential (α := α) (n + 1) t f) τ
      = blurredDifferentialRaw (α := α) n t
          (extendBlurred (α := α) (n := n + 1) (t := t)
            (blurredDifferential (α := α) (n + 1) t f)) τ := by
            rfl
    _ = blurredDifferentialRaw (α := α) n t g τ := by rw [hext]
    _ = 0 := by
          simpa [g, blurredDifferentialRaw] using
            (magnitudeDifferential_squared n
              (extendBlurred (α := α) (n := n + 2) (t := t) f) τ.1)

/-- Restrict blurred cochains along a threshold inclusion. -/
def blurredRestrict (n : Nat) {s t : Nat} (hst : s ≤ t)
    (f : BlurredChain (α := α) n t → ℤ) :
    BlurredChain (α := α) n s → ℤ :=
  fun τ => f (blurredInclusion (α := α) n hst τ)

/-- A `t`-threshold cochain vanishes above `s` if every chain of length `> s`
inside the `t`-window maps to `0`. -/
def VanishesAbove (n s t : Nat)
    (f : BlurredChain (α := α) n t → ℤ) : Prop :=
  ∀ (σ : MagnitudeChain α n) (hσt : chainLength σ ≤ t),
    s < chainLength σ → f ⟨σ, hσt⟩ = 0

/-- A `t`-cochain that vanishes above `s` induces a global extension that is
zero above `s`. -/
theorem zeroAbove_extendBlurred_of_vanishesAbove
    (n s t : Nat)
    (f : BlurredChain (α := α) n t → ℤ)
    (hvanish : VanishesAbove (α := α) n s t f) :
    ZeroAbove (α := α) n s (extendBlurred (α := α) (n := n) (t := t) f) := by
  intro σ hs
  by_cases hσt : chainLength σ ≤ t
  · simpa [extendBlurred, hσt] using hvanish σ hσt hs
  · simp [extendBlurred, hσt]

/-- A global extension that is zero above `s` induces vanishing-above-`s`
for the underlying `t`-cochain. -/
theorem vanishesAbove_of_zeroAbove_extendBlurred
    (n s t : Nat)
    (f : BlurredChain (α := α) n t → ℤ)
    (hzero : ZeroAbove (α := α) n s (extendBlurred (α := α) (n := n) (t := t) f)) :
    VanishesAbove (α := α) n s t f := by
  intro σ hσt hs
  have hz : extendBlurred (α := α) (n := n) (t := t) f σ = 0 := hzero σ hs
  simpa [extendBlurred, hσt] using hz

/-- Bridge lemma between threshold-local and global support formulations. -/
theorem vanishesAbove_iff_zeroAbove_extendBlurred
    (n s t : Nat)
    (f : BlurredChain (α := α) n t → ℤ) :
    VanishesAbove (α := α) n s t f ↔
      ZeroAbove (α := α) n s (extendBlurred (α := α) (n := n) (t := t) f) := by
  constructor
  · exact zeroAbove_extendBlurred_of_vanishesAbove (α := α) n s t f
  · exact vanishesAbove_of_zeroAbove_extendBlurred (α := α) n s t f

/-- If a `t`-cochain vanishes above `s`, extending it to all chains is the same as
extending its restricted `s`-cochain. -/
theorem extendBlurred_eq_extendBlurredRestrict_of_vanishesAbove
    (n : Nat) {s t : Nat} (hst : s ≤ t)
    (f : BlurredChain (α := α) n t → ℤ)
    (hvanish : VanishesAbove (α := α) n s t f) :
    extendBlurred (α := α) (n := n) (t := t) f =
      extendBlurred (α := α) (n := n) (t := s)
        (blurredRestrict (α := α) n hst f) := by
  funext σ
  by_cases hσt : chainLength σ ≤ t
  · by_cases hσs : chainLength σ ≤ s
    · simp [extendBlurred, blurredRestrict, blurredInclusion, hσt, hσs]
    · have hslt : s < chainLength σ := lt_of_not_ge hσs
      have hzero : f ⟨σ, hσt⟩ = 0 := hvanish σ hσt hslt
      simp [extendBlurred, hσt, hσs, hzero]
  · have hσsFalse : ¬ chainLength σ ≤ s := by
      intro hσs
      exact hσt (le_trans hσs hst)
    simp [extendBlurred, hσt, hσsFalse]

/-- Persistence compatibility for the raw blurred differential. -/
theorem blurred_persistence_commutes_raw (n : Nat) {s t : Nat} (hst : s ≤ t)
    (f : MagnitudeChain α (n + 1) → ℤ) :
    blurredRestrict (α := α) n hst (blurredDifferentialRaw (α := α) n t f) =
      blurredDifferentialRaw (α := α) n s f := by
  funext τ
  rfl

/-- Persistence compatibility for the actual blurred differential, under the
natural support condition that the `t`-cochain is already zero above `s`. -/
theorem blurred_persistence_commutes (n : Nat) {s t : Nat} (hst : s ≤ t)
    (f : BlurredChain (α := α) (n + 1) t → ℤ)
    (hvanish : VanishesAbove (α := α) (n + 1) s t f) :
    blurredRestrict (α := α) n hst (blurredDifferential (α := α) n t f) =
      blurredDifferential (α := α) n s
        (blurredRestrict (α := α) (n + 1) hst f) := by
  funext τ
  unfold blurredDifferential
  have hext :
      extendBlurred (α := α) (n := n + 1) (t := t) f =
        extendBlurred (α := α) (n := n + 1) (t := s)
          (blurredRestrict (α := α) (n + 1) hst f) :=
    extendBlurred_eq_extendBlurredRestrict_of_vanishesAbove
      (α := α) (n := n + 1) hst f hvanish
  exact congrArg (fun g => magnitudeDifferential n g τ.1) hext

/-- Vietoris-Rips style chains at threshold `t`: pairwise distance bounded by `t`. -/
def VRChain (n t : Nat) : Type u :=
  { τ : MagnitudeChain α n // ∀ i j : Fin (n + 1), MetricMagnitudeSpace.dist (τ.1 i) (τ.1 j) ≤ t }

instance instFintypeVRChain (n t : Nat) : Fintype (VRChain (α := α) n t) := by
  classical
  unfold VRChain
  infer_instance

/-- `ℓ_p` consecutive-edge path-energy of a chain. We keep the threshold in `Nat`,
so this stores the powered form `∑ dist^p` directly. -/
def lpPathEnergy (p n : Nat) (τ : MagnitudeChain α n) : Nat :=
  ∑ i : Fin n, (MetricMagnitudeSpace.dist (τ.1 i.castSucc) (τ.1 i.succ)) ^ p

/-- `ℓ_p` consecutive-edge bounded chains at threshold `t` (powered form). -/
def LPChain (p n t : Nat) : Type u :=
  { τ : MagnitudeChain α n // lpPathEnergy (α := α) p n τ ≤ t }

instance instFintypeLPChain (p n t : Nat) : Fintype (LPChain (α := α) p n t) := by
  classical
  unfold LPChain
  infer_instance

/-- The `p = 1` path-energy is exactly the chain length. -/
theorem lpPathEnergy_one_eq_chainLength (n : Nat) (τ : MagnitudeChain α n) :
    lpPathEnergy (α := α) 1 n τ = chainLength τ := by
  simp [lpPathEnergy, chainLength]

/-- Degree-preserving equivalence between the `p=1` family and blurred chains. -/
def lpChain_one_equiv_blurred (n t : Nat) :
    LPChain (α := α) 1 n t ≃ BlurredChain (α := α) n t where
  toFun := fun τ => ⟨τ.1, by simpa [lpPathEnergy_one_eq_chainLength] using τ.2⟩
  invFun := fun τ => ⟨τ.1, by simpa [lpPathEnergy_one_eq_chainLength] using τ.2⟩
  left_inv := by
    intro τ
    cases τ
    rfl
  right_inv := by
    intro τ
    cases τ
    rfl

/-- Any VR chain at scale `t` yields an `ℓ_p`-bounded chain at scale `n * t^p`. -/
def vrToLpScaled (p n t : Nat) :
    VRChain (α := α) n t → LPChain (α := α) p n (n * t ^ p)
  | ⟨τ, hVR⟩ =>
      ⟨τ, by
        unfold lpPathEnergy
        calc
          (∑ i : Fin n, (MetricMagnitudeSpace.dist (τ.1 i.castSucc) (τ.1 i.succ)) ^ p)
              ≤ (Finset.card (Finset.univ : Finset (Fin n))) * (t ^ p) := by
                simpa using
                  (Finset.sum_le_card_nsmul
                    (s := (Finset.univ : Finset (Fin n)))
                    (f := fun i : Fin n =>
                      (MetricMagnitudeSpace.dist (τ.1 i.castSucc) (τ.1 i.succ)) ^ p)
                    (n := t ^ p)
                    (h := by
                      intro i hi
                      exact Nat.pow_le_pow_left (hVR i.castSucc i.succ) p))
          _ = n * t ^ p := by simp⟩

/-- `ℓ∞` all-pair bounded chains. This is definitionally `VRChain`; the alias
keeps the interpolation vocabulary explicit. -/
abbrev LInfPairChain (n t : Nat) : Type u := VRChain (α := α) n t

instance instFintypeLInfPairChain (n t : Nat) : Fintype (LInfPairChain (α := α) n t) := by
  infer_instance

/-- Canonical equivalence: VR chains are exactly `ℓ∞` all-pair bounded chains. -/
def vrEquivLInfPairChain (n t : Nat) :
    VRChain (α := α) n t ≃ LInfPairChain (α := α) n t :=
  Equiv.refl _

/-- `ℓ∞` consecutive-edge bounded chains. This is generally weaker than VR
(`LInfPairChain`) for degree `n ≥ 2`. -/
def LInfConsecutiveChain (n t : Nat) : Type u :=
  { τ : MagnitudeChain α n // ∀ i : Fin n,
      MetricMagnitudeSpace.dist (τ.1 i.castSucc) (τ.1 i.succ) ≤ t }

instance instFintypeLInfConsecutiveChain (n t : Nat) :
    Fintype (LInfConsecutiveChain (α := α) n t) := by
  classical
  unfold LInfConsecutiveChain
  infer_instance

/-- VR chains always satisfy the `ℓ∞` consecutive-edge bound. -/
def vrToLInfConsecutive (n t : Nat) :
    VRChain (α := α) n t → LInfConsecutiveChain (α := α) n t
  | ⟨τ, hVR⟩ => ⟨τ, fun i => hVR i.castSucc i.succ⟩

/-- Any VR chain at scale `t` is a blurred chain at threshold `n * t`. -/
def vrToBlurredScaled (n t : Nat) :
    VRChain (α := α) n t → BlurredChain (α := α) n (n * t)
  | ⟨τ, hVR⟩ =>
      ⟨τ, by
        unfold chainLength
        calc
          (∑ i : Fin n, MetricMagnitudeSpace.dist (τ.1 i.castSucc) (τ.1 i.succ))
              ≤ (Finset.card (Finset.univ : Finset (Fin n))) * t := by
                simpa using
                  (Finset.sum_le_card_nsmul
                    (s := (Finset.univ : Finset (Fin n)))
                    (f := fun i : Fin n =>
                      MetricMagnitudeSpace.dist (τ.1 i.castSucc) (τ.1 i.succ))
                    (n := t)
                    (h := by
                      intro i hi
                      exact hVR i.castSucc i.succ))
          _ = n * t := by simp⟩

/-- Hypothesis: pairwise distances are controlled by chain length. -/
def PairwiseControlledByLength (n : Nat) : Prop :=
  ∀ τ : MagnitudeChain α n, ∀ i j : Fin (n + 1),
    MetricMagnitudeSpace.dist (τ.1 i) (τ.1 j) ≤ chainLength τ

/-- Under pairwise-length control, blurred chains induce VR chains at the same threshold. -/
def blurredToVR (n t : Nat) (hpair : PairwiseControlledByLength (α := α) n) :
    BlurredChain (α := α) n t → VRChain (α := α) n t
  | ⟨τ, hτ⟩ => ⟨τ, fun i j => le_trans (hpair τ i j) hτ⟩

/-- If pairwise and path-length constraints are equivalent at threshold `t`,
blurred chains and VR chains are equivalent. -/
def blurred_eq_vr_l1 (n t : Nat)
    (hpair : PairwiseControlledByLength (α := α) n)
    (hpath : ∀ τ : MagnitudeChain α n,
      (∀ i j : Fin (n + 1), MetricMagnitudeSpace.dist (τ.1 i) (τ.1 j) ≤ t) →
        chainLength τ ≤ t) :
    BlurredChain (α := α) n t ≃ VRChain (α := α) n t where
  toFun := blurredToVR (α := α) n t hpair
  invFun := fun τ => ⟨τ.1, hpath τ.1 τ.2⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl

/-- In degree `1`, pairwise distances are automatically controlled by chain length. -/
theorem pairwiseControlledByLength_one :
    PairwiseControlledByLength (α := α) 1 := by
  intro τ i j
  fin_cases i <;> fin_cases j
  · simp [chainLength, MetricMagnitudeSpace.dist_self]
  ·
    change MetricMagnitudeSpace.dist (τ.1 (0 : Fin 2)) (τ.1 (1 : Fin 2)) ≤ chainLength τ
    simp [chainLength]
  ·
    change MetricMagnitudeSpace.dist (τ.1 (1 : Fin 2)) (τ.1 (0 : Fin 2)) ≤ chainLength τ
    rw [MetricMagnitudeSpace.dist_symm (τ.1 (1 : Fin 2)) (τ.1 (0 : Fin 2))]
    simp [chainLength]
  · simp [chainLength, MetricMagnitudeSpace.dist_self]

/-- In degree `1`, the VR condition directly bounds the chain length. -/
theorem vr_implies_chainLength_le_one (t : Nat) (τ : MagnitudeChain α 1)
    (hVR : ∀ i j : Fin (1 + 1), MetricMagnitudeSpace.dist (τ.1 i) (τ.1 j) ≤ t) :
    chainLength τ ≤ t := by
  simpa [chainLength] using hVR (0 : Fin (1 + 1)) (1 : Fin (1 + 1))

/-- Concrete, hypothesis-free `Blurred ≃ VR` bridge in degree `1`. -/
def blurred_eq_vr_l1_degreeOne (t : Nat) :
    BlurredChain (α := α) 1 t ≃ VRChain (α := α) 1 t :=
  blurred_eq_vr_l1 (α := α) 1 t
    pairwiseControlledByLength_one
    (fun τ hVR => vr_implies_chainLength_le_one (α := α) t τ hVR)

/-- Degree-0 blurred chains are in bijection with the underlying points. -/
def blurredDegreeZeroEquiv (t : Nat) : BlurredChain (α := α) 0 t ≃ α where
  toFun := fun τ => τ.1.1 0
  invFun := fun x =>
    ⟨⟨fun _ => x, by
      intro i
      exact Fin.elim0 i⟩, by
      simp [chainLength]⟩
  left_inv := by
    intro τ
    cases τ with
    | mk τ hτ =>
      cases τ with
      | mk f hf =>
        apply Subtype.ext
        apply Subtype.ext
        funext i
        have hi : i = 0 := Fin.eq_zero i
        simp [hi]
  right_inv := by
    intro x
    rfl

/-- Degree-0 blurred-chain cardinality agrees with the ambient carrier cardinality. -/
theorem card_blurred_degreeZero (t : Nat) :
    Fintype.card (BlurredChain (α := α) 0 t) = Fintype.card α := by
  exact Fintype.card_congr (blurredDegreeZeroEquiv (α := α) t)

/-- Degree-0 blurred setting is consistent with the uniform weighting baseline. -/
theorem blurred_degreeZero_weighting_consistency (t : Nat) :
    magnitudeOfWeighting (uniformWeighting α) =
      Int.ofNat (Fintype.card (BlurredChain (α := α) 0 t)) := by
  rw [card_blurred_degreeZero (α := α) t]
  exact magnitudeOfWeighting_uniform α

end Magnitude
end Metrics
end HeytingLean
