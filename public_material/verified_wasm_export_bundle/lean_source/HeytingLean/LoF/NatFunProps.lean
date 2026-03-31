import HeytingLean.LambdaIR.Add1MiniCProof
import HeytingLean.LambdaIR.Add1EndToEnd
import HeytingLean.LambdaIR.DoubleMiniCProof
import HeytingLean.LambdaIR.DoubleEndToEnd
import HeytingLean.LambdaIR.SuccTwiceMiniCProof
import HeytingLean.LambdaIR.SuccTwiceEndToEnd
import HeytingLean.LambdaIR.Max01MiniCProof
import HeytingLean.LambdaIR.Max01EndToEnd
import HeytingLean.LambdaIR.Add2MiniCProof
import HeytingLean.LambdaIR.Add2EndToEnd
import HeytingLean.LambdaIR.ClampMiniCProof
import HeytingLean.LambdaIR.ClampEndToEnd
import HeytingLean.LambdaIR.Max2MiniCProof
import HeytingLean.LambdaIR.Max2EndToEnd
import HeytingLean.LambdaIR.Min2MiniCProof
import HeytingLean.LambdaIR.Min2EndToEnd
import HeytingLean.LambdaIR.RealFunMiniCProof
import HeytingLean.LambdaIR.RealFunEndToEnd
import HeytingLean.LambdaIR.NatCompileFrag
import HeytingLean.LambdaIR.Nat2CompileFrag
import HeytingLean.EndToEnd.NatFunSpec

namespace HeytingLean
namespace LoF

open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.Add1MiniCProof
open HeytingLean.LambdaIR.Add1EndToEnd
open HeytingLean.LambdaIR.DoubleMiniCProof
open HeytingLean.LambdaIR.DoubleEndToEnd
open HeytingLean.LambdaIR.SuccTwiceMiniCProof
open HeytingLean.LambdaIR.SuccTwiceEndToEnd
open HeytingLean.LambdaIR.Max01MiniCProof
open HeytingLean.LambdaIR.Max01EndToEnd
open HeytingLean.LambdaIR.Add2MiniCProof
open HeytingLean.LambdaIR.Add2EndToEnd
open HeytingLean.LambdaIR.ClampMiniCProof
open HeytingLean.LambdaIR.ClampEndToEnd
open HeytingLean.LambdaIR.Max2MiniCProof
open HeytingLean.LambdaIR.Max2EndToEnd
open HeytingLean.LambdaIR.Min2MiniCProof
open HeytingLean.LambdaIR.Min2EndToEnd
open HeytingLean.LambdaIR.RealFunMiniCProof
open HeytingLean.LambdaIR.RealFunEndToEnd
open HeytingLean.LambdaIR.NatCompileFrag
open HeytingLean.LambdaIR.Nat2CompileFrag
open HeytingLean.EndToEnd

/-- Spec for the add1 example: increments its input by one. -/
def Add1Spec (f : Nat -> Nat) : Prop :=
  ∀ n : Nat, f n = n + 1

theorem leanAdd1_spec : Add1Spec leanAdd1 := by
  intro n
  simp [leanAdd1]

/-- The compiled `add1` fragment agrees with the `n + 1` spec. -/
theorem add1_compiled_spec :
  ∀ n : Nat,
    runCompiledNatFunFrag "add1" "x" termAdd1IR n = some (n + 1) := by
  intro n
  have h := add1_end_to_end n
  simpa [Add1MiniCProof.leanAdd1] using h

/-- Spec for the doubling example. -/
def DoubleSpec (f : Nat -> Nat) : Prop :=
  ∀ n : Nat, f n = n + n

theorem leanDouble_spec : DoubleSpec leanDouble := by
  intro n
  simp [leanDouble]

/-- The compiled `double` fragment returns `n + n`. -/
theorem double_compiled_spec :
  ∀ n : Nat,
    runCompiledNatFunFrag "double" "x" termDoubleIR n = some (n + n) := by
  intro n
  have h := double_end_to_end n
  simpa [DoubleMiniCProof.leanDouble] using h

/-- Spec for the `succTwice` example. -/
def SuccTwiceSpec (f : Nat -> Nat) : Prop :=
  ∀ n : Nat, f n = n + 2

theorem leanSuccTwice_spec : SuccTwiceSpec leanSuccTwice := by
  intro n
  simp [leanSuccTwice]

/-- The compiled `succTwice` fragment returns `n + 2`. -/
theorem succTwice_compiled_spec :
  ∀ n : Nat,
    runCompiledNatFunFrag "succ_twice" "x" termSuccTwiceIR n = some (n + 2) := by
  intro n
  have h := succTwice_end_to_end n
  simpa [SuccTwiceMiniCProof.leanSuccTwice] using h

/-- Spec for the `max01` example: `1` at zero, identity otherwise. -/
def Max01Spec (f : Nat -> Nat) : Prop :=
  ∀ n : Nat, f n = (if n = 0 then 1 else n)

theorem leanMax01_spec : Max01Spec leanMax01 := by
  intro n
  simp [Max01MiniCProof.leanMax01]

/-- The compiled `max01` fragment matches its Lean definition. -/
theorem max01_compiled_spec :
  ∀ n : Nat,
    runCompiledNatFunFrag "max01" "x" termMax01IR n
      = some (if n = 0 then 1 else n) := by
  intro n
  have h := max01_end_to_end n
  simpa [Max01MiniCProof.leanMax01] using h

/-- Predicate stating that the image of a nat->nat function lies in `{0, 1}`. -/
def Boolish (f : Nat -> Nat) : Prop :=
  ∀ n : Nat, Or (f n = 0) (f n = 1)

theorem leanClamp01_boolish : Boolish leanClamp01 := by
  intro n
  by_cases h : n = 0
  · subst h
    simp [leanClamp01]
  · have hne : n ≠ 0 := h
    have h1 : leanClamp01 n = 1 := by
      simp [leanClamp01, hne]
    exact Or.inr h1

/-- The compiled MiniC clamp01 function only returns 0 or 1. -/
theorem clamp01_compiled_boolish :
  ∀ n : Nat,
    Or (runCompiledNatFunFrag "clamp01" "x" termClamp01IR n = some 0)
       (runCompiledNatFunFrag "clamp01" "x" termClamp01IR n = some 1) := by
  intro n
  have hSpec := clamp01_end_to_end n
  have hLean := leanClamp01_boolish n
  cases hLean with
  | inl h0 =>
      left
      simpa [h0] using hSpec
  | inr h1 =>
      right
      simpa [h1] using hSpec

/-- Spec for the equality-guarded `max2` example: returns `y` when the arguments
    match, otherwise returns the first argument. -/
def Max2Select (f : Nat -> Nat -> Nat) : Prop :=
  ∀ x y : Nat, And (x = y -> f x y = y) (x ≠ y -> f x y = x)

theorem leanMax2_select : Max2Select leanMax2 := by
  intro x y
  by_cases h : x = y
  · subst h
    constructor
    · intro _; simp [leanMax2]
    · intro hne; cases hne rfl
  · constructor
    · intro hxy; cases h hxy
    · intro hxy; simp [leanMax2, h]

/-- The compiled `max2` MiniC fragment satisfies the same selection property. -/
theorem max2_compiled_select :
  ∀ x y : Nat,
    And (x = y ->
      runCompiledNat2FunFrag "max2" "x" "y" termMax2IR x y = some y)
        (x ≠ y ->
      runCompiledNat2FunFrag "max2" "x" "y" termMax2IR x y = some x) := by
  intro x y
  have hRun := max2_end_to_end x y
  have hLean := leanMax2_select x y
  rcases hLean with ⟨hEq, hNe⟩
  constructor
  · intro hxy
    have hx := hEq hxy
    simpa [hx] using hRun
  · intro hxy
    have hx := hNe hxy
    simpa [hx] using hRun

/-- Spec for the addition example on two arguments. -/
def Add2Spec (f : Nat -> Nat -> Nat) : Prop :=
  ∀ x y : Nat, f x y = x + y

theorem leanAdd2_spec : Add2Spec leanAdd2 := by
  intro x y
  simp [leanAdd2]

/-- The compiled `add2` fragment returns the arithmetic sum. -/
theorem add2_compiled_spec :
  ∀ x y : Nat,
    runCompiledNat2FunFrag "add2" "x" "y" termAdd2IR x y = some (x + y) := by
  intro x y
  have h := add2_end_to_end x y
  simpa [Add2MiniCProof.leanAdd2] using h

/-- Spec for the “zero-or-sum” example: returns `0` on equality, otherwise `x + y`. -/
def XorSumSpec (f : Nat -> Nat -> Nat) : Prop :=
  ∀ x y : Nat, And (x = y -> f x y = 0) (x ≠ y -> f x y = x + y)

theorem leanXorSum_spec : XorSumSpec leanXorSum := by
  intro x y
  by_cases h : x = y
  · subst h
    constructor
    · intro _; simp [leanXorSum]
    · intro hne; cases hne rfl
  · constructor
    · intro hxy; cases h hxy
    · intro _; simp [leanXorSum, h]

/-- The compiled `xorSum` MiniC fragment satisfies the same spec. -/
theorem xorSum_compiled_spec :
  ∀ x y : Nat,
    And (x = y ->
      runCompiledNat2FunFrag "xorSum" "x" "y" termXorSumIR x y = some 0)
        (x ≠ y ->
      runCompiledNat2FunFrag "xorSum" "x" "y" termXorSumIR x y = some (x + y)) := by
  intro x y
  have hRun := xorSum_end_to_end x y
  have hLean := leanXorSum_spec x y
  rcases hLean with ⟨hEq, hNe⟩
  constructor
  · intro hxy
    have hx := hEq hxy
    simpa [hx] using hRun
  · intro hxy
    have hx := hNe hxy
    simpa [hx] using hRun

/-- Spec for the dual equality guard: returns the first argument on equality,
    otherwise the second. -/
def Min2Select (f : Nat -> Nat -> Nat) : Prop :=
  ∀ x y : Nat, And (x = y -> f x y = x) (x ≠ y -> f x y = y)

theorem leanMin2_select : Min2Select leanMin2 := by
  intro x y
  by_cases h : x = y
  · subst h
    constructor
    · intro _; simp [leanMin2]
    · intro hne; cases hne rfl
  · constructor
    · intro hxy; cases h hxy
    · intro hxy; simp [leanMin2, h]

/-- The compiled `min2` MiniC fragment satisfies the same selection property. -/
theorem min2_compiled_select :
  ∀ x y : Nat,
    And (x = y ->
      runCompiledNat2FunFrag "min2" "x" "y" termMin2IR x y = some x)
        (x ≠ y ->
      runCompiledNat2FunFrag "min2" "x" "y" termMin2IR x y = some y) := by
  intro x y
  have hRun := min2_end_to_end x y
  have hLean := leanMin2_select x y
  rcases hLean with ⟨hEq, hNe⟩
  constructor
  · intro hxy
    have hx := hEq hxy
    simpa [hx] using hRun
  · intro hxy
    have hx := hNe hxy
    simpa [hx] using hRun

end LoF
end HeytingLean
