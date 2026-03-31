import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import HeytingLean.Epiplexity.Core
import HeytingLean.Probability.InfoTheory.Conditional

namespace HeytingLean
namespace Epiplexity

open scoped BigOperators

noncomputable section

open HeytingLean.Meta.AIT
open HeytingLean.Probability
open HeytingLean.Probability.InfoTheory
open HeytingLean.Epiplexity.Info

/-!
Conditional epiplexity / time-bounded entropy (paper Definition 11).

The paper’s definition is *relative to a feasible model class* `𝒫_T` / `𝒫_T^X`.
Our core `OptimalProg` (Definition 8) packages an optimizer witness but does not yet model a
concrete “universal machine”, so for a concrete counterexample we also provide a finite-class
variant (`OptimalProgIn`, `OptimalCondProgIn`) indexed by a finite type.
-/

variable {α β : Type u} [Fintype α] [Fintype β]

/-- A coded conditional model: for each `x`, a distribution `Q(·|x)` with one global code. -/
structure CondProg (α β : Type u) [Fintype α] [Fintype β] where
  code : Program
  runtime : Nat
  dist : α → FinDist β
  distPos : ∀ x, (dist x).Pos

namespace CondProg

variable {α β : Type u} [Fintype α] [Fintype β]

/-- Program length in bits. -/
def codeLen (P : CondProg α β) : Nat :=
  codeLength P.code

/-- Feasible under a time budget `T`. -/
def Feasible (T : Nat) (P : CondProg α β) : Prop :=
  P.runtime ≤ T

end CondProg

/-- Conditional negative log-likelihood in bits for a joint outcome `(x,y)`. -/
def condNllBits (Q : α → FinDist β) (xy : α × β) : ℝ :=
  Info.nllBits (Q xy.1) xy.2

/-- Conditional cross-entropy `E_{(X,Y)}[-log₂ Q(Y|X)]` in bits. -/
def condCrossEntropyBits (PXY : FinDist (α × β)) (Q : α → FinDist β) : ℝ :=
  ∑ xy : α × β, PXY.pmf xy * condNllBits (α := α) (β := β) Q xy

/-- Two-part conditional MDL cost in bits: `|P| + E[-log₂ P(Y|X)]`. -/
def condMdlCost (PXY : FinDist (α × β)) (P : CondProg α β) : ℝ :=
  (P.codeLen : ℝ) + condCrossEntropyBits (α := α) (β := β) PXY P.dist

/-- An explicit witness of a conditional MDL-optimal program with a “shortest program” tie-break. -/
structure OptimalCondProg (T : Nat) (PXY : FinDist (α × β)) where
  P : CondProg α β
  feasible : CondProg.Feasible T P
  optimal : ∀ Q : CondProg α β, CondProg.Feasible T Q → condMdlCost (α := α) (β := β) PXY P ≤
    condMdlCost (α := α) (β := β) PXY Q
  tieBreak :
    ∀ Q : CondProg α β, CondProg.Feasible T Q →
      condMdlCost (α := α) (β := β) PXY Q = condMdlCost (α := α) (β := β) PXY P →
        P.codeLen ≤ Q.codeLen

namespace OptimalCondProg

variable {T : Nat} {PXY : FinDist (α × β)}

/-- Conditional epiplexity `S_T(Y|X)` (paper Definition 11) for an explicit optimizer witness. -/
def ST (opt : OptimalCondProg (α := α) (β := β) T PXY) : Nat :=
  opt.P.codeLen

/-- Conditional time-bounded entropy `H_T(Y|X)` (paper Definition 11) for an explicit optimizer. -/
def HT (opt : OptimalCondProg (α := α) (β := β) T PXY) : ℝ :=
  condCrossEntropyBits (α := α) (β := β) PXY opt.P.dist

/-- Total conditional MDL `MDL_T(Y|X) = S_T(Y|X) + H_T(Y|X)`. -/
def MDLT (opt : OptimalCondProg (α := α) (β := β) T PXY) : ℝ :=
  (opt.ST : ℝ) + opt.HT

end OptimalCondProg

/-!
Finite-class (“model class”) variants for concrete examples.

These match the paper’s `min_{P ∈ 𝒫_T}` intent without requiring an explicit universal machine.
-/

/-- An unconditional MDL-optimal program within a *finite* model class indexed by `ι`. -/
structure OptimalProgIn {ι : Type u} [Fintype ι] (T : Nat) (X : FinDist α) (C : ι → Prog α) where
  idx : ι
  feasible : Prog.Feasible T (C idx)
  optimal : ∀ j : ι, Prog.Feasible T (C j) → mdlCost X (C idx) ≤ mdlCost X (C j)
  tieBreak :
    ∀ j : ι, Prog.Feasible T (C j) → mdlCost X (C j) = mdlCost X (C idx) → (C idx).codeLen ≤
      (C j).codeLen

namespace OptimalProgIn

variable {ι : Type u} [Fintype ι] {T : Nat} {X : FinDist α} {C : ι → Prog α}

/-- Epiplexity `S_T(X)` inside a finite model class. -/
def ST (opt : OptimalProgIn (α := α) (T := T) X C) : Nat :=
  (C opt.idx).codeLen

/-- Time-bounded entropy `H_T(X)` inside a finite model class. -/
def HT (opt : OptimalProgIn (α := α) (T := T) X C) : ℝ :=
  Info.crossEntropyBits X (C opt.idx).dist

/-- Total MDL inside a finite model class. -/
def MDLT (opt : OptimalProgIn (α := α) (T := T) X C) : ℝ :=
  (opt.ST : ℝ) + opt.HT

end OptimalProgIn

/-- A conditional MDL-optimal program within a *finite* conditional model class indexed by `ι`. -/
structure OptimalCondProgIn {ι : Type u} [Fintype ι] (T : Nat) (PXY : FinDist (α × β))
    (C : ι → CondProg α β) where
  idx : ι
  feasible : CondProg.Feasible T (C idx)
  optimal :
    ∀ j : ι, CondProg.Feasible T (C j) →
      condMdlCost (α := α) (β := β) PXY (C idx) ≤ condMdlCost (α := α) (β := β) PXY (C j)
  tieBreak :
    ∀ j : ι, CondProg.Feasible T (C j) →
      condMdlCost (α := α) (β := β) PXY (C j) = condMdlCost (α := α) (β := β) PXY (C idx) →
        (C idx).codeLen ≤ (C j).codeLen

namespace OptimalCondProgIn

variable {ι : Type u} [Fintype ι] {T : Nat} {PXY : FinDist (α × β)} {C : ι → CondProg α β}

/-- Conditional epiplexity `S_T(Y|X)` inside a finite conditional model class. -/
def ST (opt : OptimalCondProgIn (α := α) (β := β) (T := T) PXY C) : Nat :=
  (C opt.idx).codeLen

/-- Conditional time-bounded entropy `H_T(Y|X)` inside a finite conditional model class. -/
def HT (opt : OptimalCondProgIn (α := α) (β := β) (T := T) PXY C) : ℝ :=
  condCrossEntropyBits (α := α) (β := β) PXY (C opt.idx).dist

/-- Total conditional MDL inside a finite conditional model class. -/
def MDLT (opt : OptimalCondProgIn (α := α) (β := β) (T := T) PXY C) : ℝ :=
  (opt.ST : ℝ) + opt.HT

end OptimalCondProgIn

namespace Counterexample

open Epiplexity.FinDist

open scoped BigOperators

/-! A small finite counterexample (Bool × Bool) showing the chain-rule identity can fail. -/

noncomputable def diagJoint : FinDist (Bool × Bool) where
  pmf
    | (false, false) => (1 / 2 : ℝ)
    | (true, true) => (1 / 2 : ℝ)
    | _ => 0
  nonneg := by
    intro xy
    rcases xy with ⟨a, b⟩
    cases a <;> cases b <;> simp
  sum_one := by
    classical
    simp [Fintype.sum_prod_type]
    norm_num

noncomputable def condSkew (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Bool) : FinDist Bool where
  pmf y := if y = x then p else 1 - p
  nonneg := by
    intro y
    by_cases h : y = x
    · simp [h, hp0]
    · have : 0 ≤ 1 - p := by linarith [hp1]
      simp [h, this]
  sum_one := by
    classical
    cases x <;> simp

theorem condSkew_Pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x y : Bool) :
    0 < (condSkew p (le_of_lt hp0) (le_of_lt hp1) x).pmf y := by
  by_cases h : y = x
  · subst h
    simp [condSkew, hp0]
  · have : 0 < 1 - p := by linarith
    simp [condSkew, h, this]

noncomputable def progUniform {γ : Type} [Fintype γ] [Nonempty γ] : Prog γ where
  code := [true]
  runtime := 0
  dist := uniform (α := γ)
  distPos := uniform_Pos (α := γ)

theorem nllBits_uniform {γ : Type} [Fintype γ] [Nonempty γ] (a : γ) :
    Info.nllBits (uniform (α := γ)) a = Real.log (Fintype.card γ : ℝ) / Real.log 2 := by
  have hcard_pos : (0 : ℝ) < (Fintype.card γ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hpmf_pos : 0 < (uniform (α := γ)).pmf a := by
    simpa [uniform_pmf] using (one_div_pos.mpr hcard_pos)
  unfold Info.nllBits Info.nllNat
  have hsafelog :
      InfoTheory.safeLog ((Fintype.card γ : ℝ)⁻¹) = Real.log ((Fintype.card γ : ℝ)⁻¹) :=
    InfoTheory.safeLog_of_pos (by simpa [uniform_pmf, one_div] using hpmf_pos)
  calc
    -InfoTheory.safeLog ((uniform (α := γ)).pmf a) / Real.log 2
        = -InfoTheory.safeLog ((Fintype.card γ : ℝ)⁻¹) / Real.log 2 := by
            simp [uniform_pmf, one_div]
    _ = -Real.log ((Fintype.card γ : ℝ)⁻¹) / Real.log 2 := by
          simp [hsafelog]
    _ = Real.log (Fintype.card γ : ℝ) / Real.log 2 := by
          simp [Real.log_inv]

theorem crossEntropyBits_uniform {γ : Type} [Fintype γ] [Nonempty γ]
    (X : FinDist γ) :
    Info.crossEntropyBits X (uniform (α := γ)) = Real.log (Fintype.card γ : ℝ) / Real.log 2 := by
  classical
  unfold Info.crossEntropyBits
  have hconst : ∀ a : γ, Info.nllBits (uniform (α := γ)) a = Real.log (Fintype.card γ : ℝ) / Real.log 2 :=
    nllBits_uniform (γ := γ)
  -- Constant nll under uniform; use `∑ pmf = 1`.
  calc
    (∑ a : γ, X.pmf a * Info.nllBits (uniform (α := γ)) a)
        = (∑ a : γ, X.pmf a) * (Real.log (Fintype.card γ : ℝ) / Real.log 2) := by
            simp [hconst, Finset.sum_mul]
    _ = Real.log (Fintype.card γ : ℝ) / Real.log 2 := by
          simp [X.sum_one]

theorem condCrossEntropyBits_diagJoint (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    condCrossEntropyBits (α := Bool) (β := Bool) diagJoint (condSkew p hp0 hp1)
      = Info.nllBits (condSkew p hp0 hp1 false) false := by
  classical
  unfold condCrossEntropyBits condNllBits
  have hnll :
      Info.nllBits (condSkew p hp0 hp1 true) true = Info.nllBits (condSkew p hp0 hp1 false) false := by
    unfold Info.nllBits Info.nllNat
    simp [condSkew]
  -- Only the diagonal terms contribute under `diagJoint`.
  have hsum :
      (∑ xy : Bool × Bool, diagJoint.pmf xy * Info.nllBits (condSkew p hp0 hp1 xy.1) xy.2)
        = (2⁻¹ : ℝ) * Info.nllBits (condSkew p hp0 hp1 true) true
          + (2⁻¹ : ℝ) * Info.nllBits (condSkew p hp0 hp1 false) false := by
    simp [diagJoint, condSkew, Fintype.sum_prod_type]
  -- The two nll terms are equal, so the average is the common value.
  calc
    (∑ xy : Bool × Bool, diagJoint.pmf xy * Info.nllBits (condSkew p hp0 hp1 xy.1) xy.2)
        = (2⁻¹ : ℝ) * Info.nllBits (condSkew p hp0 hp1 true) true
            + (2⁻¹ : ℝ) * Info.nllBits (condSkew p hp0 hp1 false) false := hsum
    _ = (2⁻¹ : ℝ) * Info.nllBits (condSkew p hp0 hp1 false) false
          + (2⁻¹ : ℝ) * Info.nllBits (condSkew p hp0 hp1 false) false := by
          simp [hnll]
    _ = Info.nllBits (condSkew p hp0 hp1 false) false := by ring

/-- Concrete counterexample: the “chain rule” identity fails for these finite model classes. -/
theorem chain_rule_fails :
    ∃ (T : Nat)
      (optXY : OptimalProgIn (α := Bool × Bool) (T := T) diagJoint (fun _ : PUnit => progUniform))
      (optX : OptimalProgIn (α := Bool) (T := T) (uniform (α := Bool)) (fun _ : PUnit => progUniform))
      (optY : OptimalCondProgIn (α := Bool) (β := Bool) (T := T) diagJoint
        (fun _ : PUnit =>
          { code := [true]
            runtime := 0
            dist := condSkew (3 / 4) (by norm_num) (by norm_num)
            distPos := by
              intro x y
              exact condSkew_Pos (p := 3 / 4) (by norm_num) (by norm_num) x y }))
      ,
      (OptimalProgIn.HT optXY - OptimalProgIn.HT optX) ≠ OptimalCondProgIn.HT optY := by
  refine ⟨0, ?_, ?_, ?_, ?_⟩
  · refine
      { idx := ()
        feasible := by simp [Prog.Feasible, progUniform]
        optimal := by intro j hj; cases j; simp
        tieBreak := by intro j hj hcost; cases j; simp }
  · refine
      { idx := ()
        feasible := by simp [Prog.Feasible, progUniform]
        optimal := by intro j hj; cases j; simp
        tieBreak := by intro j hj hcost; cases j; simp }
  · refine
      { idx := ()
        feasible := by simp [CondProg.Feasible]
        optimal := by intro j hj; cases j; simp
        tieBreak := by intro j hj hcost; cases j; simp }
  · -- Compute the two sides: LHS is `2 - 1 = 1`, RHS is `-log(3/4)/log 2 < 1`.
    have hHX :
        OptimalProgIn.HT (α := Bool) (T := 0) (X := uniform (α := Bool)) (C := fun _ : PUnit => progUniform)
            { idx := ()
              feasible := by simp [Prog.Feasible, progUniform]
              optimal := by intro j hj; cases j; simp
              tieBreak := by intro j hj hcost; cases j; simp }
          = 1 := by
      -- `H_T(X)` for the singleton class is cross-entropy vs uniform on `Bool`.
      unfold OptimalProgIn.HT progUniform
      -- `card Bool = 2`.
      have hlog2_pos : 0 < Real.log (2 : ℝ) := by
        have : (1 : ℝ) < 2 := by norm_num
        simpa using Real.log_pos this
      have hlog2_ne0 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2_pos
      calc
        Info.crossEntropyBits (uniform (α := Bool)) (uniform (α := Bool))
            = Real.log (Fintype.card Bool : ℝ) / Real.log 2 := by
                simpa using (crossEntropyBits_uniform (γ := Bool) (X := uniform (α := Bool)))
        _ = 1 := by simp [Fintype.card_bool, hlog2_ne0]
    have hHXY :
        OptimalProgIn.HT (α := Bool × Bool) (T := 0) (X := diagJoint) (C := fun _ : PUnit => progUniform)
            { idx := ()
              feasible := by simp [Prog.Feasible, progUniform]
              optimal := by intro j hj; cases j; simp
              tieBreak := by intro j hj hcost; cases j; simp }
          = 2 := by
      unfold OptimalProgIn.HT progUniform
      have hlog2_pos : 0 < Real.log (2 : ℝ) := by
        have : (1 : ℝ) < 2 := by norm_num
        simpa using Real.log_pos this
      have hlog2_ne0 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2_pos
      have hcard :
          Real.log (Fintype.card (Bool × Bool) : ℝ) / Real.log 2 = (2 : ℝ) := by
        have h4pow : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        calc
          Real.log (Fintype.card (Bool × Bool) : ℝ) / Real.log 2
              = Real.log 4 / Real.log 2 := by
                  simp [Fintype.card_prod, Fintype.card_bool]
          _ = Real.log ((2 : ℝ) ^ 2) / Real.log 2 := by simp [h4pow]
          _ = ((2 : ℝ) * Real.log 2) / Real.log 2 := by simp [Real.log_pow]
          _ = 2 := by simp [hlog2_ne0]
      calc
        Info.crossEntropyBits diagJoint (uniform (α := Bool × Bool))
            = Real.log (Fintype.card (Bool × Bool) : ℝ) / Real.log 2 := by
                simpa using (crossEntropyBits_uniform (γ := Bool × Bool) (X := diagJoint))
        _ = 2 := hcard
    have hHYX :
        OptimalCondProgIn.HT (α := Bool) (β := Bool) (T := 0) (PXY := diagJoint)
            (C := fun _ : PUnit =>
              { code := [true]
                runtime := 0
                dist := condSkew (3 / 4) (by norm_num) (by norm_num)
                distPos := by
                  intro x y
                  exact condSkew_Pos (p := 3 / 4) (by norm_num) (by norm_num) x y })
            { idx := ()
              feasible := by simp [CondProg.Feasible]
              optimal := by intro j hj; cases j; simp
              tieBreak := by intro j hj hcost; cases j; simp }
          = Info.nllBits (condSkew (3 / 4) (by norm_num) (by norm_num) false) false := by
      unfold OptimalCondProgIn.HT
      simpa using (condCrossEntropyBits_diagJoint (p := 3 / 4) (by norm_num) (by norm_num))
    -- Reduce LHS to `1`.
    have :
        (2 : ℝ) - 1 ≠ Info.nllBits (condSkew (3 / 4) (by norm_num) (by norm_num) false) false := by
      have hlog2_pos : 0 < Real.log (2 : ℝ) := by
        have : (1 : ℝ) < 2 := by norm_num
        simpa using Real.log_pos this
      have hlog2_ne0 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt hlog2_pos
      have h21 : (2 : ℝ) - 1 = 1 := by norm_num
      -- Show `nllBits (condSkew 3/4 false) false < 1`.
      have hPos34 : 0 < (3 / 4 : ℝ) := by norm_num
      have hPos12 : 0 < (1 / 2 : ℝ) := by norm_num
      have hlt : (1 / 2 : ℝ) < (3 / 4 : ℝ) := by norm_num
      have hlog12 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        have : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
        simp [this, Real.log_inv]
      have hdiv_lt : (-Real.log (3 / 4 : ℝ)) / Real.log 2 < 1 := by
        have hlog_lt : Real.log (1 / 2 : ℝ) < Real.log (3 / 4 : ℝ) :=
          Real.log_lt_log hPos12 hlt
        have hneg : -Real.log (3 / 4 : ℝ) < -Real.log (1 / 2 : ℝ) := by
          linarith [hlog_lt]
        have hneg' : -Real.log (3 / 4 : ℝ) < Real.log 2 := by
          simpa [hlog12] using hneg
        have hdiv : (-Real.log (3 / 4 : ℝ)) / Real.log 2 < Real.log 2 / Real.log 2 :=
          div_lt_div_of_pos_right hneg' hlog2_pos
        have h1 : Real.log 2 / Real.log 2 = (1 : ℝ) := by simp [hlog2_ne0]
        simpa [h1] using hdiv
      have hnll :
          Epiplexity.Info.nllBits (condSkew (3 / 4) (by norm_num) (by norm_num) false) false =
            (-Real.log (3 / 4 : ℝ)) / Real.log 2 := by
        unfold Epiplexity.Info.nllBits Epiplexity.Info.nllNat
        simp [condSkew]
      have hnll_lt :
          Epiplexity.Info.nllBits (condSkew (3 / 4) (by norm_num) (by norm_num) false) false < 1 := by
        simpa [hnll] using hdiv_lt
      have hnll_ne :
          Epiplexity.Info.nllBits (condSkew (3 / 4) (by norm_num) (by norm_num) false) false ≠ 1 :=
        ne_of_lt hnll_lt
      -- `2 - 1 = 1` and `nllBits(...) ≠ 1`.
      simpa [h21] using (Ne.symm hnll_ne)
    -- assemble
    simpa [hHXY, hHX, hHYX] using this

end Counterexample

end

end Epiplexity
end HeytingLean
