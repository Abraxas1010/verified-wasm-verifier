import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Fintype.Card
import HeytingLean.Epiplexity.Core

namespace HeytingLean
namespace Epiplexity

open scoped BigOperators

open HeytingLean.Probability
open HeytingLean.Epiplexity.Info

noncomputable section

namespace BitStr

instance (n : Nat) : Nonempty (BitStr n) := by
  refine ⟨⟨0, ?_⟩⟩
  exact Nat.pow_pos (a := 2) (n := n) (Nat.succ_pos 1)

/-- A constant-size feasible program implementing the uniform distribution on `BitStr n`. -/
noncomputable def uniformProg (n : Nat) : Prog (BitStr n) where
  code := [true]
  runtime := 0
  dist := FinDist.uniform (α := BitStr n)
  distPos := FinDist.uniform_Pos (α := BitStr n)

@[simp] theorem uniformProg_codeLen (n : Nat) :
    (uniformProg n).codeLen = 1 := by
  simp [uniformProg, Prog.codeLen, HeytingLean.Meta.AIT.codeLength, HeytingLean.Meta.AIT.Program.length]

theorem entropyNat_uniform (n : Nat) :
    InfoTheory.FinDist.entropy (FinDist.uniform (α := BitStr n))
      = Real.log (Fintype.card (BitStr n) : ℝ) := by
  classical
  have hPos : (FinDist.uniform (α := BitStr n)).Pos := FinDist.uniform_Pos (α := BitStr n)
  have hent :
      InfoTheory.FinDist.entropy (FinDist.uniform (α := BitStr n))
        = - (∑ a : BitStr n,
              (FinDist.uniform (α := BitStr n)).pmf a *
                Real.log ((FinDist.uniform (α := BitStr n)).pmf a)) :=
    InfoTheory.FinDist.entropy_eq_neg_sum_mul_log_of_Pos _ hPos
  calc
    InfoTheory.FinDist.entropy (FinDist.uniform (α := BitStr n))
        = - (∑ a : BitStr n,
              (FinDist.uniform (α := BitStr n)).pmf a *
                Real.log ((FinDist.uniform (α := BitStr n)).pmf a)) := hent
    _ = -((Fintype.card (BitStr n) : ℝ) *
          ((1 / (Fintype.card (BitStr n) : ℝ)) * Real.log (1 / (Fintype.card (BitStr n) : ℝ)))) := by
          simp [Finset.sum_const]
    _ = -Real.log (1 / (Fintype.card (BitStr n) : ℝ)) := by
          simp [one_div]
    _ = Real.log (Fintype.card (BitStr n) : ℝ) := by
          simp [one_div, Real.log_inv]

theorem entropyBits_uniform (n : Nat) :
    Info.entropyBits (FinDist.uniform (α := BitStr n)) = n := by
  classical
  unfold Info.entropyBits
  have hnat :
      InfoTheory.FinDist.entropy (FinDist.uniform (α := BitStr n))
        = Real.log (Fintype.card (BitStr n) : ℝ) :=
    entropyNat_uniform (n := n)
  have hlog2_pos : 0 < Real.log (2 : ℝ) := by
    have : (1 : ℝ) < 2 := by norm_num
    simpa using Real.log_pos this
  have hlog2_ne0 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2_pos
  calc
    InfoTheory.FinDist.entropy (FinDist.uniform (α := BitStr n)) / Real.log 2
        = Real.log (Fintype.card (BitStr n) : ℝ) / Real.log 2 := by
              simp [hnat]
    _ = ((n : ℝ) * Real.log 2) / Real.log 2 := by
          simp [BitStr, Nat.cast_pow, Real.log_pow]
    _ = n := by
          simp [hlog2_ne0]

theorem crossEntropyBits_uniform (n : Nat) (X : InfoTheory.FinDist (BitStr n)) :
    Info.crossEntropyBits X (FinDist.uniform (α := BitStr n)) = n := by
  classical
  have hPos : (FinDist.uniform (α := BitStr n)).Pos := FinDist.uniform_Pos (α := BitStr n)
  have hceNat :
      Info.crossEntropyNat X (FinDist.uniform (α := BitStr n))
        = -∑ a : BitStr n, X.pmf a * Real.log ((FinDist.uniform (α := BitStr n)).pmf a) :=
    Info.crossEntropyNat_eq_neg_sum_mul_log_of_Pos (p := X) (q := FinDist.uniform (α := BitStr n)) hPos
  have hnat :
      Info.crossEntropyNat X (FinDist.uniform (α := BitStr n))
        = Real.log (Fintype.card (BitStr n) : ℝ) := by
    calc
      Info.crossEntropyNat X (FinDist.uniform (α := BitStr n))
          = -∑ a : BitStr n, X.pmf a * Real.log (1 / (Fintype.card (BitStr n) : ℝ)) := by
                simpa [FinDist.uniform_pmf] using hceNat
      _ = -(∑ a : BitStr n, X.pmf a) * Real.log (1 / (Fintype.card (BitStr n) : ℝ)) := by
            simp [Finset.sum_mul]
      _ = Real.log (Fintype.card (BitStr n) : ℝ) := by
            simp [X.sum_one, one_div, Real.log_inv]
  have hlog2_pos : 0 < Real.log (2 : ℝ) := by
    have : (1 : ℝ) < 2 := by norm_num
    simpa using Real.log_pos this
  have hlog2_ne0 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2_pos
  have hbits :
      Info.crossEntropyBits X (FinDist.uniform (α := BitStr n))
        = Info.crossEntropyNat X (FinDist.uniform (α := BitStr n)) / Real.log 2 :=
    Info.crossEntropyBits_eq_crossEntropyNat_div_log2 (p := X) (q := FinDist.uniform (α := BitStr n))
  calc
    Info.crossEntropyBits X (FinDist.uniform (α := BitStr n))
        = Info.crossEntropyNat X (FinDist.uniform (α := BitStr n)) / Real.log 2 := hbits
    _ = Real.log (Fintype.card (BitStr n) : ℝ) / Real.log 2 := by simp [hnat]
    _ = ((n : ℝ) * Real.log 2) / Real.log 2 := by
          simp [BitStr, Nat.cast_pow, Real.log_pow]
    _ = n := by
          simp [hlog2_ne0]

theorem lemma15_MDLinf_le (n T : Nat) (X : InfoTheory.FinDist (BitStr n)) :
    MDLinf (α := BitStr n) T X ≤ (n : ℝ) + (uniformProg n).codeLen := by
  have hP : Prog.Feasible T (uniformProg n) := by
    simp [uniformProg, Prog.Feasible]
  have hce : Info.crossEntropyBits X (uniformProg n).dist = n := by
    simpa [uniformProg] using (crossEntropyBits_uniform (n := n) (X := X))
  have hcost : mdlCost X (uniformProg n) = (uniformProg n).codeLen + (n : ℝ) := by
    simp [mdlCost, hce]
  have hle : MDLinf (α := BitStr n) T X ≤ mdlCost X (uniformProg n) :=
    MDLinf_le_mdlCost (α := BitStr n) (T := T) (X := X) (P := uniformProg n) hP
  calc
    MDLinf (α := BitStr n) T X ≤ (uniformProg n).codeLen + (n : ℝ) := by
      simpa [hcost] using hle
    _ = (n : ℝ) + (uniformProg n).codeLen := by
      ring

theorem lemma16_HT_bounds (n T : Nat) :
    ∀ opt : OptimalProg (α := BitStr n) T (FinDist.uniform (α := BitStr n)),
      (n : ℝ) ≤ opt.HT ∧ opt.HT ≤ (n : ℝ) + (uniformProg n).codeLen := by
  intro opt
  constructor
  · -- Lower bound: cross-entropy ≥ entropy, and entropy(uniform)=n.
    have hEnt : Info.entropyBits (FinDist.uniform (α := BitStr n)) = n :=
      entropyBits_uniform (n := n)
    have hge :
        Info.entropyBits (FinDist.uniform (α := BitStr n))
          ≤ Info.crossEntropyBits (FinDist.uniform (α := BitStr n)) opt.P.dist :=
      Info.crossEntropyBits_ge_entropyBits
        (p := FinDist.uniform (α := BitStr n))
        (q := opt.P.dist)
        (FinDist.uniform_Pos (α := BitStr n))
        opt.P.distPos
    simpa [OptimalProg.HT, hEnt] using hge
  · -- Upper bound: optimality vs the uniform witness, then drop the nonnegative code length of `opt`.
    have hFeas : Prog.Feasible T (uniformProg n) := by
      simp [uniformProg, Prog.Feasible]
    have hopt :
        mdlCost (FinDist.uniform (α := BitStr n)) opt.P
          ≤ mdlCost (FinDist.uniform (α := BitStr n)) (uniformProg n) :=
      opt.optimal (uniformProg n) hFeas
    have hce_unif :
        Info.crossEntropyBits (FinDist.uniform (α := BitStr n)) (uniformProg n).dist = n := by
      simpa [uniformProg] using
        crossEntropyBits_uniform (n := n) (X := FinDist.uniform (α := BitStr n))
    have hlen_nonneg : (0 : ℝ) ≤ (opt.P.codeLen : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have : opt.HT ≤ (uniformProg n).codeLen + (n : ℝ) := by
      have hcost_rhs :
          mdlCost (FinDist.uniform (α := BitStr n)) (uniformProg n)
            = (uniformProg n).codeLen + (n : ℝ) := by
              simp [mdlCost, hce_unif]
      have hcost_lhs :
          mdlCost (FinDist.uniform (α := BitStr n)) opt.P
            = (opt.P.codeLen : ℝ) + opt.HT := by
              simp [mdlCost, OptimalProg.HT]
      have hsum : (opt.P.codeLen : ℝ) + opt.HT ≤ (uniformProg n).codeLen + (n : ℝ) := by
        simpa [hcost_lhs, hcost_rhs] using hopt
      exact le_of_add_le_of_nonneg_right hsum hlen_nonneg
    simpa [add_comm, add_left_comm, add_assoc] using this

end BitStr

end

end Epiplexity
end HeytingLean
