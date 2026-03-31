import HeytingLean.Quantum.QState
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-
Kraus/CPTP scaffolding used by the qRelEnt plan.  We only implement the pieces
needed to express channels as explicit Kraus lists and to map density matrices.
-/

namespace HeytingLean
namespace Quantum

open Matrix Complex
open scoped Matrix BigOperators

noncomputable section

namespace ActiveInference

/-- Helper predicate recording that a rectangular matrix implements an isometry. -/
def IsometryMatrix {m k : ℕ} (V : Matrix (Fin m) (Fin k) ℂ) : Prop :=
  V.conjTranspose * V = 1

end ActiveInference

/-- Finite Kraus channel represented by an explicit list of Kraus operators. -/
structure KrausChannel (n m : ℕ) where
  ops : List (Matrix (Fin m) (Fin n) ℂ)
  /-- Σᵢ Kᵢ† Kᵢ = I ensures complete positivity + trace preservation. -/
  tracePreserving :
    (∑ i : Fin ops.length, (ops.get i).conjTranspose * ops.get i) =
      (1 : Matrix (Fin n) (Fin n) ℂ)

variable {n m : ℕ}

namespace KrausChannel

variable (Φ : KrausChannel n m)

/-- Convenience alias for the number of Kraus operators. -/
@[simp] abbrev numOps : ℕ := Φ.ops.length

/-- Access the `i`-th Kraus operator (as a matrix) using a `Fin` index. -/
def op (i : Fin Φ.numOps) : Matrix (Fin m) (Fin n) ℂ :=
  Φ.ops.get i

@[simp] lemma op_eq_get (i : Fin Φ.numOps) :
    Φ.op i = Φ.ops.get i := rfl

/-- Helper capturing the Σᵢ Kᵢ† Kᵢ witness. -/
def tpSum : Matrix (Fin n) (Fin n) ℂ :=
  ∑ i : Fin Φ.numOps, (Φ.op i).conjTranspose * Φ.op i

lemma tpSum_eq_sum_ops :
    Φ.tpSum = ∑ i : Fin Φ.numOps, (Φ.op i).conjTranspose * Φ.op i := rfl

@[simp] lemma tpSum_eq_one : Φ.tpSum = 1 := by
  classical
  simpa [tpSum, op, numOps] using Φ.tracePreserving

/-- Apply a Kraus channel to a matrix (typically a density operator). -/
def map (ρ : Mat n) : Mat m :=
  ∑ i : Fin Φ.numOps, Φ.op i * ρ * (Φ.op i).conjTranspose

lemma map_eq_sum (ρ : Mat n) :
    Φ.map ρ = ∑ i : Fin Φ.numOps, Φ.op i * ρ * (Φ.op i).conjTranspose := rfl

@[simp] lemma map_zero : Φ.map (0 : Mat n) = 0 := by
  classical
  simp [map, Matrix.mul_zero, Matrix.zero_mul]

/-- `map` preserves trace (uses the Kraus trace-preserving law). -/
lemma trace_map (ρ : Mat n) : Matrix.trace (Φ.map ρ) = Matrix.trace ρ := by
  classical
  -- Expand `map` and push `trace` through the finite sum.
  unfold KrausChannel.map
  set term : Fin Φ.numOps → Mat m :=
    fun i => Φ.op i * ρ * (Φ.op i).conjTranspose
  have htraceSum :
      Matrix.trace (∑ i : Fin Φ.numOps, term i) =
        ∑ i : Fin Φ.numOps, Matrix.trace (term i) := by
    exact map_sum (Matrix.traceAddMonoidHom (Fin m) ℂ) term (Finset.univ : Finset (Fin Φ.numOps))
  -- Cycle each term: `Tr(K ρ K†) = Tr(K† K ρ)`.
  have hcycle :
      (∑ i : Fin Φ.numOps, Matrix.trace (term i)) =
        ∑ i : Fin Φ.numOps, Matrix.trace ((Φ.op i).conjTranspose * Φ.op i * ρ) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    simpa [term, Matrix.mul_assoc] using
      (Matrix.trace_mul_cycle (A := Φ.op i) (B := ρ) (C := (Φ.op i).conjTranspose))
  -- Fold the Kraus sum using linearity of trace and distributivity of multiplication.
  have htraceLin :
      (∑ i : Fin Φ.numOps, Matrix.trace ((Φ.op i).conjTranspose * Φ.op i * ρ)) =
        Matrix.trace (∑ i : Fin Φ.numOps, (Φ.op i).conjTranspose * Φ.op i * ρ) := by
    -- Apply `map_sum` in the reverse direction.
    symm
    have h :=
      map_sum (Matrix.traceAddMonoidHom (Fin n) ℂ)
        (fun i : Fin Φ.numOps => (Φ.op i).conjTranspose * Φ.op i * ρ)
        (Finset.univ : Finset (Fin Φ.numOps))
    exact h
  calc
    Matrix.trace (∑ i : Fin Φ.numOps, term i)
        = ∑ i : Fin Φ.numOps, Matrix.trace (term i) := htraceSum
    _ = ∑ i : Fin Φ.numOps, Matrix.trace ((Φ.op i).conjTranspose * Φ.op i * ρ) := hcycle
    _ = Matrix.trace (∑ i : Fin Φ.numOps, (Φ.op i).conjTranspose * Φ.op i * ρ) := htraceLin
    _ = Matrix.trace ((∑ i : Fin Φ.numOps, (Φ.op i).conjTranspose * Φ.op i) * ρ) := by
          simp [Finset.sum_mul, Matrix.mul_assoc]
    _ = Matrix.trace (Φ.tpSum * ρ) := rfl
    _ = Matrix.trace (1 * ρ) := by simp
    _ = Matrix.trace ρ := by simp

/-- `map` sends Hermitian matrices to Hermitian matrices. -/
lemma isHermitian_map {ρ : Mat n} (hρ : ρ.IsHermitian) : (Φ.map ρ).IsHermitian := by
  classical
  -- Each term `K ρ K†` is Hermitian, and sums preserve Hermitian-ness.
  have hterm :
      ∀ i : Fin Φ.numOps, (Φ.op i * ρ * (Φ.op i).conjTranspose).IsHermitian := by
    intro i
    -- Use `isHermitian_conjTranspose_mul_mul` with `B := (Φ.op i)†`.
    simpa [Matrix.mul_assoc, Matrix.conjTranspose_conjTranspose] using
      (Matrix.isHermitian_conjTranspose_mul_mul (B := (Φ.op i).conjTranspose) hρ)
  -- Sum over all `i` (rewrite as a `Finset.univ` sum and induct).
  unfold KrausChannel.map
  have hs :
      Matrix.IsHermitian
        ((Finset.univ : Finset (Fin Φ.numOps)).sum fun i =>
          Φ.op i * ρ * (Φ.op i).conjTranspose) := by
    refine Finset.induction_on (s := (Finset.univ : Finset (Fin Φ.numOps))) ?base ?step
    · simp
    · intro a s ha hs
      have ha' : (Φ.op a * ρ * (Φ.op a).conjTranspose).IsHermitian := hterm a
      simpa [Finset.sum_insert, ha] using Matrix.IsHermitian.add ha' hs
  -- The goal is definitionally the sum over `Finset.univ`.
  exact hs

/-- `map` sends `PosSemidef` matrices to `PosSemidef` matrices. -/
lemma posSemidef_map {ρ : Mat n} (hρ : PosSemidef ρ) : PosSemidef (Φ.map ρ) := by
  classical
  have hterm :
      ∀ i : Fin Φ.numOps, PosSemidef (Φ.op i * ρ * (Φ.op i).conjTranspose) := by
    intro i
    -- Conjugation preserves our `PosSemidef` predicate (proved in `QState`).
    simpa [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using
      (PosSemidef.mul_mul_conjTranspose_same (m := Fin m) (n := Fin n) hρ (Φ.op i))
  unfold KrausChannel.map
  -- Use the `PosSemidef.sum` lemma from `QState` with `s := univ`.
  simpa using
    (PosSemidef.sum (ι := Fin m) (s := (Finset.univ : Finset (Fin Φ.numOps)))
      (f := fun i : Fin Φ.numOps => Φ.op i * ρ * (Φ.op i).conjTranspose)
      (by
        intro i hi
        exact hterm i))

/-- Apply a Kraus channel to a density operator, producing a density operator. -/
def mapDensity (ρ : Density n) : Density m := by
  classical
  refine
    { mat := Φ.map ρ.mat
      hermitian := Φ.isHermitian_map (ρ := ρ.mat) ρ.hermitian
      traceOne := ?_
      posSemidef := Φ.posSemidef_map (ρ := ρ.mat) ρ.posSemidef }
  have := Φ.trace_map (ρ := ρ.mat)
  -- Rewrite via trace preservation, then use `ρ.traceOne`.
  simpa [Density.mat] using this.trans ρ.traceOne

/-- The block-stacked isometry whose rows record the Kraus operators. -/
def isometryMatrix :
    Matrix (Fin (m * Φ.numOps)) (Fin n) ℂ :=
  fun idx j =>
    let pr := finProdFinEquiv.symm idx
    Φ.op pr.2 pr.1 j

lemma isometryMatrix_isometry :
    ActiveInference.IsometryMatrix (Φ.isometryMatrix) := by
  classical
  unfold ActiveInference.IsometryMatrix
  ext i j
  have hstep₁ :
      ((Φ.isometryMatrix).conjTranspose * Φ.isometryMatrix) i j =
        ∑ idx : Fin (m * Φ.numOps),
          star (Φ.isometryMatrix idx i) * Φ.isometryMatrix idx j := by
    simp [Matrix.mul_apply]
  have hstep₂ :
      (∑ idx : Fin (m * Φ.numOps),
          star (Φ.isometryMatrix idx i) * Φ.isometryMatrix idx j) =
        ∑ pair : Fin m × Fin Φ.numOps,
          star (Φ.op pair.2 pair.1 i) * Φ.op pair.2 pair.1 j := by
    classical
    have :=
      Fintype.sum_equiv (finProdFinEquiv (m:=m) (n:=Φ.numOps)).symm
        (fun idx : Fin (m * Φ.numOps) =>
          star (Φ.isometryMatrix idx i) * Φ.isometryMatrix idx j)
        (fun pair : Fin m × Fin Φ.numOps =>
          star (Φ.op pair.2 pair.1 i) * Φ.op pair.2 pair.1 j)
        (by
          intro idx
          simp [isometryMatrix])
    simpa [isometryMatrix] using this
  have hstep₃ :
      (∑ pair : Fin m × Fin Φ.numOps,
          star (Φ.op pair.2 pair.1 i) * Φ.op pair.2 pair.1 j) =
        ∑ pair : Fin Φ.numOps × Fin m,
          star (Φ.op pair.1 pair.2 i) * Φ.op pair.1 pair.2 j := by
    have :=
      Fintype.sum_equiv (Equiv.prodComm (Fin m) (Fin Φ.numOps))
        (fun pair : Fin m × Fin Φ.numOps =>
          star (Φ.op pair.2 pair.1 i) * Φ.op pair.2 pair.1 j)
        (fun pair : Fin Φ.numOps × Fin m =>
          star (Φ.op pair.1 pair.2 i) * Φ.op pair.1 pair.2 j)
        (by
          intro pair
          simp)
    simpa using this
  have hstep₄ :
      (∑ pair : Fin Φ.numOps × Fin m,
          star (Φ.op pair.1 pair.2 i) * Φ.op pair.1 pair.2 j) =
        ∑ l : Fin Φ.numOps, ∑ r : Fin m,
          star ((Φ.op l) r i) * (Φ.op l) r j := by
    classical
    simpa [Finset.univ_product_univ] using
      (Finset.sum_product (Finset.univ : Finset (Fin Φ.numOps))
        (Finset.univ : Finset (Fin m))
        (fun p : Fin Φ.numOps × Fin m =>
          star ((Φ.op p.1) p.2 i) * (Φ.op p.1) p.2 j))
  have hstep₅ :
      (∑ l : Fin Φ.numOps, ∑ r : Fin m,
          star ((Φ.op l) r i) * (Φ.op l) r j) =
        (∑ l : Fin Φ.numOps,
          (Φ.op l).conjTranspose * Φ.op l) i j := by
    classical
    have hcongr :
        (∑ l : Fin Φ.numOps, ∑ r : Fin m,
            star ((Φ.op l) r i) * (Φ.op l) r j) =
          ∑ l : Fin Φ.numOps,
            ((Φ.op l).conjTranspose * Φ.op l) i j := by
      refine Finset.sum_congr rfl ?_
      intro l _
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    have happly :
        ∑ l : Fin Φ.numOps,
            ((Φ.op l).conjTranspose * Φ.op l) i j =
          (∑ l : Fin Φ.numOps,
            (Φ.op l).conjTranspose * Φ.op l) i j := by
      simpa [Finset.mem_univ] using
        (Matrix.sum_apply i j (Finset.univ : Finset (Fin Φ.numOps))
          (fun l : Fin Φ.numOps => (Φ.op l).conjTranspose * Φ.op l)).symm
    exact hcongr.trans happly
  have hfinal :
      ((Φ.isometryMatrix).conjTranspose * Φ.isometryMatrix) i j =
        (∑ l : Fin Φ.numOps,
          (Φ.op l).conjTranspose * Φ.op l) i j := by
    calc
      ((Φ.isometryMatrix).conjTranspose * Φ.isometryMatrix) i j
          = ∑ idx : Fin (m * Φ.numOps),
              star (Φ.isometryMatrix idx i) * Φ.isometryMatrix idx j := hstep₁
      _ = ∑ pair : Fin m × Fin Φ.numOps,
              star (Φ.op pair.2 pair.1 i) * Φ.op pair.2 pair.1 j := hstep₂
      _ = ∑ pair : Fin Φ.numOps × Fin m,
              star (Φ.op pair.1 pair.2 i) * Φ.op pair.1 pair.2 j := hstep₃
      _ = ∑ l : Fin Φ.numOps, ∑ r : Fin m,
              star ((Φ.op l) r i) * (Φ.op l) r j := hstep₄
      _ = (∑ l : Fin Φ.numOps,
              (Φ.op l).conjTranspose * Φ.op l) i j := hstep₅
  have htpEntry :
      (∑ l : Fin Φ.numOps,
          (Φ.op l).conjTranspose * Φ.op l) i j =
        Φ.tpSum i j :=
    congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j)
      Φ.tpSum_eq_sum_ops.symm
  have hfinal' :
      ((Φ.isometryMatrix).conjTranspose * Φ.isometryMatrix) i j =
        Φ.tpSum i j :=
    hfinal.trans htpEntry
  have htp :
      Φ.tpSum i j = (1 : Matrix (Fin n) (Fin n) ℂ) i j :=
    congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) Φ.tpSum_eq_one
  exact hfinal'.trans htp

@[simp] def id (n : ℕ) : KrausChannel n n := by
  classical
  refine ⟨[1], ?_⟩
  ext i j
  simp

end KrausChannel

end

end Quantum
end HeytingLean
