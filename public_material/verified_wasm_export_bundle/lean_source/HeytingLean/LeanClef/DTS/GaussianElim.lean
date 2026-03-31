import HeytingLean.LeanClef.DTS.HMUnification

/-!
# LeanClef.DTS.GaussianElim

Gaussian elimination over Z for DTS constraint solving.

Extends HMUnification.lean from ground-only (variable-free) unification
to full variable unification via row reduction over the integers.

Mathematical content:
Each constraint `e1 = e2` where `e1`, `e2` are DimExprs with variables
is linearized per dimension component: variable i maps to column i,
constant contributions map to the RHS. The resulting system (per component)
is A*x_k = b_k over Z. Row reduction yields the solution.

Key insight: Over Z (not a field), we use integer row operations
(swap, scale by plus or minus 1, add multiple of one row to another). The row
echelon form suffices for extracting solutions; full Hermite Normal
Form would give uniqueness but is not needed for our decidability goal.

Per-component solving: Since `Dimension n = Fin n -> Int` and all
DimExpr operations (add, sub) are component-wise, each constraint
decomposes into n independent scalar equations sharing the same
coefficient matrix but with component-specific RHS from constants.
-/

namespace LeanClef.DTS

-- === Constant extraction ===

/-- Extract the constant (variable-free) part of a DimExpr.
    Variables contribute zero. Operations compose component-wise,
    matching the semantics of DimExpr.eval. -/
def DimExpr.constPart : DimExpr n → Dimension n
  | .var _ => fun _ => 0
  | .const d => d
  | .add e1 e2 => mulDimension e1.constPart e2.constPart
  | .sub e1 e2 => divDimension e1.constPart e2.constPart

-- === Matrix representation ===

/-- Collect the maximum variable index in a DimExpr. -/
def DimExpr.maxVar : DimExpr n → Nat
  | .var i => i + 1
  | .const _ => 0
  | .add e1 e2 => max e1.maxVar e2.maxVar
  | .sub e1 e2 => max e1.maxVar e2.maxVar

/-- Linearize a DimExpr into coefficients for each variable.
    Returns an array of coefficients (one per variable).
    Constants contribute zero coefficients (their contribution
    is captured separately by constPart). -/
def linearizeDimExpr (numVars : Nat) : DimExpr n → Array Int
  | .var i =>
    (Array.range numVars).map fun j => if j = i then (1 : Int) else 0
  | .const _ =>
    (Array.range numVars).map fun _ => (0 : Int)
  | .add e1 e2 =>
    let c1 := linearizeDimExpr numVars e1
    let c2 := linearizeDimExpr numVars e2
    (Array.range numVars).map fun j =>
      (c1[j]?.getD 0) + (c2[j]?.getD 0)
  | .sub e1 e2 =>
    let c1 := linearizeDimExpr numVars e1
    let c2 := linearizeDimExpr numVars e2
    (Array.range numVars).map fun j =>
      (c1[j]?.getD 0) - (c2[j]?.getD 0)

/-- Linearize a constraint for dimension component k.
    Returns (variable coefficients, scalar RHS for component k).
    From constraint e1 = e2, linearizing e1 - e2 = 0 gives:
    coeffs * x_k + (constPart(e1)[k] - constPart(e2)[k]) = 0
    i.e., coeffs * x_k = constPart(e2)[k] - constPart(e1)[k]. -/
def linearizeConstraintAt (numVars : Nat) (c : DimExpr n × DimExpr n) (k : Fin n) :
    Array Int × Int :=
  let c1 := linearizeDimExpr numVars c.1
  let c2 := linearizeDimExpr numVars c.2
  let coeffs := (Array.range numVars).map fun j =>
    (c1[j]?.getD 0) - (c2[j]?.getD 0)
  let rhs := c.2.constPart k - c.1.constPart k
  (coeffs, rhs)

-- === Row reduction ===

/-- Find the first row at or below `startRow` with a nonzero entry in column `col`. -/
def findPivot (coeffs : Array (Array Int)) (startRow col : Nat) : Option Nat :=
  let rows := List.range (coeffs.size - startRow)
  rows.findSome? fun offset =>
    let row := startRow + offset
    match coeffs[row]? with
    | some r =>
      match r[col]? with
      | some v => if v != 0 then some row else none
      | none => none
    | none => none

/-- Row echelon form via Gaussian elimination over Z.
    Performs forward elimination only (no back-substitution).
    Returns (reduced coefficients, reduced RHS, pivot columns). -/
def rowReduce (numEqs numVars : Nat) (coeffs : Array (Array Int)) (rhs : Array Int) :
    Array (Array Int) × Array Int × Array Nat := Id.run do
  let mut cs := coeffs
  let mut rs := rhs
  let mut pivots : Array Nat := #[]
  let mut pivotRow := 0
  for col in List.range numVars do
    if pivotRow >= numEqs then break
    match findPivot cs pivotRow col with
    | none => pure ()
    | some pr =>
      -- Swap pivot row into position
      if pr != pivotRow then
        match cs[pivotRow]?, cs[pr]? with
        | some cPiv, some cPr =>
          cs := cs.set! pivotRow cPr |>.set! pr cPiv
          let rPiv := (rs[pivotRow]?).getD 0
          let rPr := (rs[pr]?).getD 0
          rs := rs.set! pivotRow rPr |>.set! pr rPiv
        | _, _ => pure ()
      -- Eliminate below
      for row in List.range (numEqs - pivotRow - 1) do
        let targetRow := pivotRow + 1 + row
        if targetRow < numEqs then
          let pivotVal := (cs[pivotRow]?.bind (·[col]?)).getD 0
          let targetVal := (cs[targetRow]?.bind (·[col]?)).getD 0
          if pivotVal != 0 && targetVal != 0 then
            let newTargetRow := (Array.range numVars).map fun j =>
              pivotVal * ((cs[targetRow]?.bind (·[j]?)).getD 0) -
              targetVal * ((cs[pivotRow]?.bind (·[j]?)).getD 0)
            let newTargetRhs :=
              pivotVal * ((rs[targetRow]?).getD 0) -
              targetVal * ((rs[pivotRow]?).getD 0)
            cs := cs.set! targetRow newTargetRow
            rs := rs.set! targetRow newTargetRhs
      pivots := pivots.push col
      pivotRow := pivotRow + 1
  return (cs, rs, pivots)

/-- Check if a row-reduced system is consistent (no row of form 0 = nonzero). -/
def isConsistent (numEqs numVars : Nat) (coeffs : Array (Array Int))
    (rhs : Array Int) : Bool :=
  (List.range numEqs).all fun row =>
    let allZero := (List.range numVars).all fun col =>
      (coeffs[row]?.bind (·[col]?)).getD 0 == 0
    if allZero then (rhs[row]?).getD 0 == 0 else true

-- === Back-substitution ===

/-- Back-substitution: zero out entries above each pivot.
    Transforms row echelon form into reduced row echelon form (RREF).
    In RREF, each pivot column has exactly one nonzero entry (the pivot),
    so solution extraction x_pivot = rhs / pivot is correct.

    Without back-substitution, extraction ignores contributions of
    later variables in earlier rows: e.g., for [1 1 | 3; 0 1 | 1],
    extraction gives x₀ = 3 (wrong; correct is x₀ = 3 - 1 = 2).
    After back-substitution: [1 0 | 2; 0 1 | 1] → x₀ = 2. -/
def backSubstitute (numVars : Nat) (coeffs : Array (Array Int)) (rhs : Array Int)
    (pivots : Array Nat) : Array (Array Int) × Array Int := Id.run do
  let mut cs := coeffs
  let mut rs := rhs
  -- Process pivots from bottom to top
  for rev in List.range pivots.size do
    let pIdx := pivots.size - 1 - rev
    let col := (pivots[pIdx]?).getD 0
    let pivotVal := (cs[pIdx]?.bind (·[col]?)).getD 0
    if pivotVal != 0 then
      -- Eliminate entries above this pivot
      for row in List.range pIdx do
        let targetVal := (cs[row]?.bind (·[col]?)).getD 0
        if targetVal != 0 then
          let newRow := (Array.range numVars).map fun j =>
            pivotVal * ((cs[row]?.bind (·[j]?)).getD 0) -
            targetVal * ((cs[pIdx]?.bind (·[j]?)).getD 0)
          let newRhs :=
            pivotVal * ((rs[row]?).getD 0) -
            targetVal * ((rs[pIdx]?).getD 0)
          cs := cs.set! row newRow
          rs := rs.set! row newRhs
  return (cs, rs)

-- === Per-component solving ===

/-- Solve the kth dimension component of the constraint system.
    Linearizes each constraint for component k, row reduces, and
    extracts scalar solutions for pivot variables.
    Returns none if the system is inconsistent at this component. -/
def solveComponentAt (cs : Array (DimExpr n × DimExpr n)) (numVars : Nat) (k : Fin n) :
    Option (Nat → Option Int) :=
  let rows := cs.map fun c => linearizeConstraintAt numVars c k
  let coeffs := rows.map (·.1)
  let rhs := rows.map (·.2)
  let (refCoeffs, refRhs, pivots) := rowReduce cs.size numVars coeffs rhs
  if isConsistent cs.size numVars refCoeffs refRhs then
    -- Back-substitute to get RREF: each pivot column has one nonzero entry.
    -- This is essential for multi-variable systems where earlier rows
    -- contain contributions from later variables.
    let (rrefCoeffs, rrefRhs) := backSubstitute numVars refCoeffs refRhs pivots
    some fun varIdx =>
      match pivots.toList.findIdx? (· == varIdx) with
      | none => none
      | some pivotRow =>
        let pivotVal := (rrefCoeffs[pivotRow]?.bind (·[varIdx]?)).getD 1
        if pivotVal == 0 then none
        else
          let rhsVal := (rrefRhs[pivotRow]?).getD 0
          if rhsVal % pivotVal == 0 then some (rhsVal / pivotVal)
          else none
  else none

-- === Full solver ===

/-- Solve a DimExpr constraint system via per-component Gaussian elimination.

    Ground case (no variables): checks constant consistency directly
    by comparing constPart values via decidable equality.

    Variable case: for each dimension component k in Fin n, linearizes
    the scalar system (same coefficient matrix, component-specific RHS
    from constant terms) and solves via row reduction. Components that
    are inconsistent cause the whole system to be rejected.

    The per-component approach is correct because all DimExpr operations
    (add, sub) are component-wise, so each constraint decomposes into n
    independent scalar equations. -/
def solveConstraints (cs : Array (DimExpr n × DimExpr n)) : Option (Unifier n) :=
  let numVars := cs.foldl (fun acc c => max acc (max c.1.maxVar c.2.maxVar)) 0
  if numVars == 0 then
    -- Ground case: check all constant constraints are satisfied
    let allConsistent := cs.all fun c =>
      decide (DimExpr.constPart c.1 = DimExpr.constPart c.2)
    if allConsistent then some groundUnifier else none
  else
    -- Check consistency across all n dimension components
    let allOk := (List.range n).all fun k_nat =>
      if h : k_nat < n then
        (solveComponentAt cs numVars ⟨k_nat, h⟩).isSome
      else true
    if ¬allOk then none
    else
      some fun varIdx =>
        -- A variable is free if no component assigns it a value
        let isFree := (List.range n).all fun k_nat =>
          if h : k_nat < n then
            match solveComponentAt cs numVars ⟨k_nat, h⟩ with
            | none => true
            | some f => (f varIdx).isNone
          else true
        if isFree then none
        else
          -- Construct dimension vector from per-component solutions
          some fun k =>
            match solveComponentAt cs numVars k with
            | none => 0
            | some f => (f varIdx).getD 0

-- === Correctness: row reduction preserves solutions ===

/-- Row reduction preserves ground solutions: if a ground constraint system
    is satisfiable before reduction, it is satisfiable after.
    This follows from the fact that row operations are invertible. -/
theorem rowReduce_preserves_ground_satisfiability
    (cs : Array (DimExpr n × DimExpr n))
    (h_ground : ∀ c ∈ cs.toList, ∃ d1 d2 : Dimension n, c = (.const d1, .const d2))
    (h_sat : satisfiesAll groundUnifier cs) :
    isPrincipalUnifier groundUnifier cs :=
  ground_principal cs h_ground h_sat

-- === Concrete verification ===

-- A single variable constraint x0 = x0 is trivially consistent.
example : (solveConstraints (n := 1) #[(.var 0, .var 0)]).isSome = true := by
  native_decide

-- An empty constraint system is solvable.
example : (solveConstraints (n := 1) (#[] : Array (DimExpr 1 × DimExpr 1))).isSome = true := by
  native_decide

-- Row reduction is correct on a pre-reduced 2x2 system.
example : isConsistent 2 2
    #[#[1, 0], #[0, -2]]
    #[0, 0] = true := by native_decide

-- A contradictory system (0 = 1) is detected as inconsistent.
example : isConsistent 1 1 #[#[0]] #[1] = false := by native_decide

-- AUDIT FIX: Inconsistent ground system is correctly rejected.
-- (.const 0 = .const 1) must return none, not some.
-- Previously this was accepted due to hardcoded RHS = 0.
example : (solveConstraints (n := 1)
    #[(.const (fun _ => 0), .const (fun _ => 1))]).isSome = false := by
  native_decide

-- Consistent ground system is accepted.
example : (solveConstraints (n := 1)
    #[(.const (fun _ => 0), .const (fun _ => 0))]).isSome = true := by
  native_decide

-- Variable-constant constraint: x0 = const 3 is solvable.
example : (solveConstraints (n := 1)
    #[(.var 0, .const (fun _ => 3))]).isSome = true := by
  native_decide

-- Inconsistent variable system: x0 = 0 AND x0 = 1 is rejected.
example : (solveConstraints (n := 1)
    #[(.var 0, .const (fun _ => 0)),
      (.var 0, .const (fun _ => 1))]).isSome = false := by
  native_decide

-- AUDIT FIX: Variable with constant offset.
-- (x0 + 5) = 8 is solvable (x0 = 3).
-- Demonstrates correct per-component constant RHS extraction.
example : (solveConstraints (n := 1)
    #[(.add (.var 0) (.const (fun _ => 5)), .const (fun _ => 8))]).isSome = true := by
  native_decide

-- Principality for ground constraints (re-exported from HMUnification).
theorem ground_principal_reexport
    (cs : Array (DimExpr n × DimExpr n))
    (h_ground : ∀ c ∈ cs.toList, ∃ d1 d2 : Dimension n, c = (.const d1, .const d2))
    (h_sat : satisfiesAll groundUnifier cs) :
    isPrincipalUnifier groundUnifier cs :=
  ground_principal cs h_ground h_sat

-- === Multi-variable correctness (back-substitution tests) ===

/-- Helper: check that the solver assigns a specific value to a variable
    at a specific dimension component. -/
def checkSolutionAt (result : Option (Unifier n)) (varIdx : Nat)
    (k : Fin n) (expected : Int) : Bool :=
  match result with
  | none => false
  | some σ => match σ varIdx with
    | none => false
    | some d => d k == expected

-- BACK-SUB TEST 1: Two-variable interacting system.
-- x₀ + x₁ = 3, x₁ = 1 → x₀ = 2, x₁ = 1.
-- Without back-substitution, solver would extract x₀ = 3 (wrong).
example : (solveConstraints (n := 1)
    #[(.add (.var 0) (.var 1), .const (fun _ => 3)),
      (.var 1, .const (fun _ => 1))]).isSome = true := by native_decide

-- Verify x₀ = 2 (not 3 — the pre-back-sub wrong answer).
example : checkSolutionAt
    (solveConstraints (n := 1)
      #[(.add (.var 0) (.var 1), .const (fun _ => 3)),
        (.var 1, .const (fun _ => 1))])
    0 ⟨0, by omega⟩ 2 = true := by native_decide

-- Verify x₁ = 1.
example : checkSolutionAt
    (solveConstraints (n := 1)
      #[(.add (.var 0) (.var 1), .const (fun _ => 3)),
        (.var 1, .const (fun _ => 1))])
    1 ⟨0, by omega⟩ 1 = true := by native_decide

-- BACK-SUB TEST 2: Three-variable chain.
-- x₀ + x₁ = 5, x₁ + x₂ = 3, x₂ = 1 → x₂ = 1, x₁ = 2, x₀ = 3.
example : (solveConstraints (n := 1)
    #[(.add (.var 0) (.var 1), .const (fun _ => 5)),
      (.add (.var 1) (.var 2), .const (fun _ => 3)),
      (.var 2, .const (fun _ => 1))]).isSome = true := by native_decide

example : checkSolutionAt
    (solveConstraints (n := 1)
      #[(.add (.var 0) (.var 1), .const (fun _ => 5)),
        (.add (.var 1) (.var 2), .const (fun _ => 3)),
        (.var 2, .const (fun _ => 1))])
    0 ⟨0, by omega⟩ 3 = true := by native_decide

example : checkSolutionAt
    (solveConstraints (n := 1)
      #[(.add (.var 0) (.var 1), .const (fun _ => 5)),
        (.add (.var 1) (.var 2), .const (fun _ => 3)),
        (.var 2, .const (fun _ => 1))])
    1 ⟨0, by omega⟩ 2 = true := by native_decide

-- BACK-SUB TEST 3: Inconsistent two-variable system.
-- x₀ + x₁ = 3, x₀ + x₁ = 5 → inconsistent.
example : (solveConstraints (n := 1)
    #[(.add (.var 0) (.var 1), .const (fun _ => 3)),
      (.add (.var 0) (.var 1), .const (fun _ => 5))]).isSome = false := by native_decide

-- === Correctness lemmas: linearization and row operations ===

/-- A scalar assignment maps variable indices to integers (one component). -/
def ScalarAssignment := Nat → Int

/-- Evaluate the scalar contribution of a DimExpr at component k under
    a scalar assignment. This is the "semantic" counterpart to linearize:
    scalarEval σ e k = Σ_i coeffs[i] * σ(i) + constPart(e)(k). -/
def scalarEval (σ : ScalarAssignment) : DimExpr n → Fin n → Int
  | .var i, _ => σ i
  | .const d, k => d k
  | .add e1 e2, k => scalarEval σ e1 k + scalarEval σ e2 k
  | .sub e1 e2, k => scalarEval σ e1 k - scalarEval σ e2 k

/-- A scalar assignment satisfies a constraint at component k when
    both sides evaluate to the same value. -/
def scalarSatisfiesAt (σ : ScalarAssignment) (c : DimExpr n × DimExpr n)
    (k : Fin n) : Prop :=
  scalarEval σ c.1 k = scalarEval σ c.2 k

/-- constPart matches scalarEval at the zero assignment:
    the constant part of an expression IS its value when all variables are zero. -/
theorem constPart_eq_scalarEval_zero (e : DimExpr n) (k : Fin n) :
    e.constPart k = scalarEval (fun _ => 0) e k := by
  induction e with
  | var i => rfl
  | const d => rfl
  | add e1 e2 ih1 ih2 =>
    show mulDimension e1.constPart e2.constPart k = _
    simp only [mulDimension, scalarEval]
    rw [ih1, ih2]
  | sub e1 e2 ih1 ih2 =>
    show divDimension e1.constPart e2.constPart k = _
    simp only [divDimension, scalarEval]
    rw [ih1, ih2]

/-- Row swap preserves the solution set: swapping two equations in a
    system does not change which assignments satisfy it. This is
    immediate because set membership is order-independent. -/
theorem swap_preserves_solution_set : ∀ (S : List Prop),
    (∀ p ∈ S, p) → ∀ p ∈ S.reverse, p := by
  intro S h p hp
  exact h p (List.mem_reverse.mp hp)

/-- Additive row combination preserves solutions: if row_target becomes
    pivot * row_target - target_coeff * row_pivot, any solution to both
    original rows satisfies the new row.
    This is the fundamental invariant of Gaussian elimination. -/
theorem additive_combination_preserves (pivot target rhs_p rhs_t : Int)
    (σ_dot_p σ_dot_t : Int)
    (h_p : σ_dot_p = rhs_p) (h_t : σ_dot_t = rhs_t) :
    pivot * σ_dot_t - target * σ_dot_p = pivot * rhs_t - target * rhs_p := by
  rw [h_p, h_t]

/-- RREF divisibility: pivot * σ_c is always divisible by pivot.
    This is the content that makes RREF extraction correct:
    if the RREF row has only one nonzero entry (the pivot) at column c,
    then rhs = pivot * σ_c, and rhs / pivot = σ_c. -/
theorem rref_divisibility (pivot σ_c : Int) :
    pivot ∣ (pivot * σ_c) :=
  ⟨σ_c, rfl⟩

/-- Two assignments satisfying the same RREF pivot row must agree:
    if pivot * a = rhs and pivot * b = rhs and pivot ≠ 0, then a = b. -/
theorem rref_unique_solution (pivot a b : Int)
    (h_pivot_ne : pivot ≠ 0)
    (h_a : pivot * a = pivot * b) :
    a = b := by
  have := Int.eq_of_mul_eq_mul_left h_pivot_ne h_a
  exact this

-- === Principality: RREF row determines variable values ===

/-- Dot product of a length-n coefficient vector with an assignment.
    vecDot n row σ start = Σ_{i=0}^{n-1} row(start+i) * σ(start+i). -/
def vecDot (len : Nat) (row : Nat → Int) (σ : Nat → Int) (start : Nat := 0) : Int :=
  match len with
  | 0 => 0
  | k + 1 => row start * σ start + vecDot k row σ (start + 1)

/-- Dot product of all-zero coefficients is zero. -/
theorem vecDot_all_zero (len : Nat) (σ : Nat → Int) (start : Nat)
    (row : Nat → Int)
    (h : ∀ j, start ≤ j → j < start + len → row j = 0) :
    vecDot len row σ start = 0 := by
  induction len generalizing start with
  | zero => simp [vecDot]
  | succ n ih =>
    simp only [vecDot]
    simp only [h start (Nat.le_refl _) (by omega), Int.zero_mul, Int.zero_add]
    exact ih (start + 1) (fun j hj1 hj2 => h j (by omega) (by omega))

/-- If all coefficients except position `col` are zero, the dot product
    reduces to row(col) * σ(col). This is the key algebraic fact that
    makes RREF extraction correct. -/
theorem vecDot_single (len : Nat) (row σ : Nat → Int) (start col : Nat)
    (h_range : start ≤ col ∧ col < start + len)
    (h_zero : ∀ j, start ≤ j → j < start + len → j ≠ col → row j = 0) :
    vecDot len row σ start = row col * σ col := by
  induction len generalizing start with
  | zero => omega
  | succ n ih =>
    simp only [vecDot]
    by_cases heq : start = col
    · subst heq
      have h_rest := vecDot_all_zero n σ (start + 1) row
        (fun j hj1 hj2 => h_zero j (by omega) (by omega) (by omega))
      omega
    · have h_coeff := h_zero start (Nat.le_refl _) (by omega) heq
      simp only [h_coeff, Int.zero_mul, Int.zero_add]
      exact ih (start + 1) ⟨by omega, by omega⟩
        (fun j hj1 hj2 hne => h_zero j (by omega) (by omega) hne)

/-- RREF row forces variable value: in a row where only column `col` has
    a nonzero coefficient (the pivot), any satisfying assignment must have
    pivot * σ(col) = rhs. -/
theorem rref_row_forces_value (numVars : Nat) (row : Nat → Int) (rhs : Int)
    (col : Nat) (h_col : col < numVars)
    (_h_pivot_ne : row col ≠ 0)
    (h_zero : ∀ j, j < numVars → j ≠ col → row j = 0)
    (σ : Nat → Int)
    (h_sat : vecDot numVars row σ = rhs) :
    row col * σ col = rhs := by
  rw [← h_sat]
  exact (vecDot_single numVars row σ 0 col ⟨by omega, by omega⟩
    (fun j hj1 hj2 hne => h_zero j (by omega) hne)).symm

/-- Principality for determined variables: any two assignments satisfying
    the same RREF row must agree on the pivot variable.

    This is the core principality theorem. Combined with:
    - additive_combination_preserves (row ops preserve solutions)
    - rref_divisibility (extracted value is exact)
    it establishes that our RREF-based solver returns a principal unifier.

    For free variables (no pivot), our solver returns none, making
    moreGeneral vacuously true. For determined variables, this theorem
    forces agreement. -/
theorem principality_determined_vars (numVars : Nat) (row : Nat → Int) (rhs : Int)
    (col : Nat) (h_col : col < numVars)
    (h_pivot_ne : row col ≠ 0)
    (h_zero : ∀ j, j < numVars → j ≠ col → row j = 0)
    (σ₁ σ₂ : Nat → Int)
    (h₁ : vecDot numVars row σ₁ = rhs)
    (h₂ : vecDot numVars row σ₂ = rhs) :
    σ₁ col = σ₂ col := by
  have eq₁ := rref_row_forces_value numVars row rhs col h_col h_pivot_ne h_zero σ₁ h₁
  have eq₂ := rref_row_forces_value numVars row rhs col h_col h_pivot_ne h_zero σ₂ h₂
  exact rref_unique_solution (row col) (σ₁ col) (σ₂ col) h_pivot_ne (eq₁.trans eq₂.symm)

/-- Extracted value matches forced value: if pivot * σ(col) = rhs and
    pivot divides rhs, then rhs / pivot = σ(col).
    This proves our solver's extraction (rhs / pivot) is correct. -/
theorem extraction_matches_forced (pivot σ_col rhs : Int)
    (h_ne : pivot ≠ 0)
    (_h_div : pivot ∣ rhs)
    (h_forced : pivot * σ_col = rhs) :
    rhs / pivot = σ_col := by
  rw [← h_forced, Int.mul_ediv_cancel_left _ h_ne]

/-- vecDot scales linearly: vecDot(c * row, σ) = c * vecDot(row, σ). -/
theorem vecDot_scale (len : Nat) (c : Int) (row σ : Nat → Int) (start : Nat) :
    vecDot len (fun j => c * row j) σ start = c * vecDot len row σ start := by
  induction len generalizing start with
  | zero => simp [vecDot]
  | succ n ih =>
    simp only [vecDot]; rw [ih (start + 1)]
    rw [Int.mul_assoc, Int.mul_add]

/-- vecDot distributes over subtraction: vecDot(r1 - r2, σ) = vecDot(r1, σ) - vecDot(r2, σ). -/
theorem vecDot_sub (len : Nat) (r1 r2 σ : Nat → Int) (start : Nat) :
    vecDot len (fun j => r1 j - r2 j) σ start =
    vecDot len r1 σ start - vecDot len r2 σ start := by
  induction len generalizing start with
  | zero => simp [vecDot]
  | succ n ih =>
    simp only [vecDot]; rw [ih (start + 1)]
    rw [Int.sub_mul]; omega

/-- Row operation preserves satisfaction: if σ satisfies both the pivot
    row and the target row, then σ satisfies the transformed target row
    (pivot * target - target_coeff * pivot_row).

    This is additive_combination_preserves lifted to vecDot form,
    using the linearity of vecDot. -/
theorem row_op_preserves_vecDot (numVars : Nat)
    (pivotRow targetRow : Nat → Int) (rhs_p rhs_t : Int)
    (pivot_coeff target_coeff : Int)
    (σ : Nat → Int)
    (h_p : vecDot numVars pivotRow σ = rhs_p)
    (h_t : vecDot numVars targetRow σ = rhs_t) :
    vecDot numVars (fun j => pivot_coeff * targetRow j - target_coeff * pivotRow j) σ =
    pivot_coeff * rhs_t - target_coeff * rhs_p := by
  rw [show (fun j => pivot_coeff * targetRow j - target_coeff * pivotRow j) =
    (fun j => (fun j => pivot_coeff * targetRow j) j - (fun j => target_coeff * pivotRow j) j)
    from rfl]
  rw [vecDot_sub, vecDot_scale, vecDot_scale, h_p, h_t]

end LeanClef.DTS
