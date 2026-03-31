import HeytingLean.LeanCP.RealWorld.BarrettReduceVerified
import HeytingLean.LeanCP.Lang.CSemantics
import HeytingLean.LeanCP.VCG.SWPSound
import Mathlib.Tactic

namespace HeytingLean.LeanCP.RealWorld

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

/-- PQClean's `q⁻¹ mod 2^16` constant for ML-KEM. -/
def montgomeryQInv : Int := -3327

/-- Absolute value of PQClean's `q⁻¹ mod 2^16` constant. -/
def montgomeryQInvAbs : Int := 3327

/-- Two's-complement modulus governing the ML-KEM Montgomery kernel. -/
def montgomeryModulus : Int := Int.ofNat (uintModulus .I16)

/-- Low-word signed truncation used by the Montgomery kernel. -/
def montgomeryTruncate (a : Int) : Int :=
  wrapSignedInt .I16 (-(wrapSignedInt .I16 a * montgomeryQInvAbs))

/-- Arithmetic Montgomery reduction prototype on the current LeanCP surface. -/
def montgomeryReduceInt (a : Int) : Int :=
  Int.shiftRight (a - montgomeryTruncate a * barrettQ) 16

def montgomeryTruncateExpr : CExpr :=
  .cast (.intSized .Signed .I16)
    (.binop .sub
      (.intLit 0)
      (.binop .mul
        (.cast (.intSized .Signed .I16) (.var "a"))
        (.intLit montgomeryQInvAbs)))

def montgomeryReduceExpr : CExpr :=
  .binop .shr
    (.binop .sub
      (.var "a")
      (.binop .mul (.var "t") (.intLit barrettQ)))
    (.intLit 16)

def montgomeryReduceBody : CStmt :=
  .seq
    (.assign (.var "t") montgomeryTruncateExpr)
    (.seq
      (.assign (.var "t") montgomeryReduceExpr)
      (.ret (.var "t")))

def montgomeryReduceSpec (a : Int) : SFunSpec where
  name := "montgomery_reduce"
  params := [("a", .int)]
  retType := .int
  pre := fun st => st.lookupVar "a" = some (.int a)
  post := fun ret _ => ret = .int (montgomeryReduceInt a)
  body := montgomeryReduceBody

theorem montgomeryReduce_noBranch : NoBranch montgomeryReduceBody := by
  simp [NoBranch, montgomeryReduceBody]

private theorem evalBinOp_mul_int_int' (a b : Int) :
    evalBinOp .mul (.int a) (.int b) = some (.int (a * b)) := by
  rfl

private theorem evalBinOp_sub_int_int' (a b : Int) :
    evalBinOp .sub (.int a) (.int b) = some (.int (a - b)) := by
  rfl

private theorem evalBinOp_shr_int_16 (a : Int) :
    evalBinOp .shr (.int a) (.int 16) = some (.int (Int.shiftRight a 16)) := by
  rfl

theorem wrapSignedInt_modEq (a : Int) :
    wrapSignedInt .I16 a ≡ a [ZMOD montgomeryModulus] := by
  rw [Int.modEq_iff_dvd]
  unfold wrapSignedInt montgomeryModulus uintModulus
  set modulus : Int := Int.ofNat (Nat.shiftLeft 1 IntSize.I16.bits)
  set half : Int := Int.ofNat (Nat.shiftLeft 1 (IntSize.I16.bits - 1))
  set u : Int := a % modulus
  have hu : modulus ∣ a - u := by
    exact Int.dvd_self_sub_of_emod_eq (by simp [u])
  by_cases hlt : u < half
  · change modulus ∣ a - (if a.emod modulus < half then a.emod modulus else a.emod modulus - modulus)
    have haemod : a.emod modulus = a % modulus := rfl
    have huemod : a.emod modulus = u := by simpa [haemod] using (show a % modulus = u by simp [u])
    have hwrap : (if a.emod modulus < half then a.emod modulus else a.emod modulus - modulus) = u := by
      simp [huemod, hlt]
    simpa [hwrap] using hu
  · have hmod : modulus ∣ modulus := dvd_rfl
    have hadd : modulus ∣ (a - u) + modulus := Int.dvd_add hu hmod
    change modulus ∣ a - (if a.emod modulus < half then a.emod modulus else a.emod modulus - modulus)
    have haemod : a.emod modulus = a % modulus := rfl
    have huemod : a.emod modulus = u := by simpa [haemod] using (show a % modulus = u by simp [u])
    have hwrap : (if a.emod modulus < half then a.emod modulus else a.emod modulus - modulus) = u - modulus := by
      simp [huemod, hlt]
    have hsub : a - (u - modulus) = (a - u) + modulus := by ring
    simpa [hwrap, hsub] using hadd

theorem montgomeryQInv_correct :
    barrettQ * montgomeryQInv ≡ 1 [ZMOD montgomeryModulus] := by
  native_decide

theorem montgomeryTruncate_modEq (a : Int) :
    montgomeryTruncate a ≡ a * montgomeryQInv [ZMOD montgomeryModulus] := by
  have hInner : wrapSignedInt .I16 a * montgomeryQInvAbs ≡ a * montgomeryQInvAbs [ZMOD montgomeryModulus] :=
    (wrapSignedInt_modEq a).mul_right montgomeryQInvAbs
  have hNeg :
      -(wrapSignedInt .I16 a * montgomeryQInvAbs) ≡ -(a * montgomeryQInvAbs)
        [ZMOD montgomeryModulus] := by
    exact hInner.neg
  have hWrap :
      wrapSignedInt .I16 (-(wrapSignedInt .I16 a * montgomeryQInvAbs)) ≡
        -(wrapSignedInt .I16 a * montgomeryQInvAbs) [ZMOD montgomeryModulus] :=
    wrapSignedInt_modEq (-(wrapSignedInt .I16 a * montgomeryQInvAbs))
  simpa [montgomeryTruncate, montgomeryQInv, mul_assoc] using hWrap.trans hNeg

theorem montgomeryNumerator_dvd (a : Int) :
    montgomeryModulus ∣ a - montgomeryTruncate a * barrettQ := by
  have hMul :
      montgomeryTruncate a * barrettQ ≡ (a * montgomeryQInv) * barrettQ
        [ZMOD montgomeryModulus] :=
    (montgomeryTruncate_modEq a).mul_right barrettQ
  have hConst : montgomeryQInv * barrettQ ≡ 1 [ZMOD montgomeryModulus] := by
    simpa [mul_comm] using montgomeryQInv_correct
  have hRhs :
      (a * montgomeryQInv) * barrettQ ≡ a * 1 [ZMOD montgomeryModulus] := by
    simpa [mul_assoc] using (Int.ModEq.mul_left a hConst)
  have hNum :
      a - montgomeryTruncate a * barrettQ ≡ 0 [ZMOD montgomeryModulus] := by
    have hEq : montgomeryTruncate a * barrettQ ≡ a [ZMOD montgomeryModulus] := by
      simpa using hMul.trans hRhs
    have hZero : a - montgomeryTruncate a * barrettQ ≡ a - a [ZMOD montgomeryModulus] := by
      exact Int.ModEq.sub Int.ModEq.rfl hEq
    simpa using hZero
  exact Int.modEq_zero_iff_dvd.mp hNum

private theorem shiftRight_16_eq_ediv (a : Int) :
    Int.shiftRight a 16 = a / montgomeryModulus := by
  have hmod : montgomeryModulus = 65536 := by
    native_decide
  cases a using Int.rec with
  | ofNat n =>
      simp [hmod, Int.shiftRight, Nat.shiftRight_eq_div_pow]
  | negSucc n =>
      rw [hmod, Int.shiftRight, Int.negSucc_eq, Int.negSucc_eq]
      omega

theorem montgomeryReduce_eq_ediv (a : Int) :
    montgomeryReduceInt a =
      (a - montgomeryTruncate a * barrettQ) / montgomeryModulus := by
  simpa [montgomeryReduceInt] using
    shiftRight_16_eq_ediv (a - montgomeryTruncate a * barrettQ)

theorem montgomeryReduce_exact_mul (a : Int) :
    montgomeryReduceInt a * montgomeryModulus =
      a - montgomeryTruncate a * barrettQ := by
  have hdiv : montgomeryModulus ∣ a - montgomeryTruncate a * barrettQ :=
    montgomeryNumerator_dvd a
  have hcancel :
      ((a - montgomeryTruncate a * barrettQ) / montgomeryModulus) * montgomeryModulus =
        a - montgomeryTruncate a * barrettQ := by
    simpa using Int.ediv_mul_cancel hdiv
  simpa [montgomeryReduce_eq_ediv] using hcancel

theorem montgomeryReduce_congruent (a : Int) :
    montgomeryReduceInt a * montgomeryModulus ≡ a [ZMOD barrettQ] := by
  have hZero : montgomeryTruncate a * barrettQ ≡ 0 [ZMOD barrettQ] := by
    exact Int.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right (dvd_refl barrettQ) (montgomeryTruncate a))
  have hNum : a - montgomeryTruncate a * barrettQ ≡ a [ZMOD barrettQ] := by
    simpa using (Int.ModEq.sub Int.ModEq.rfl hZero)
  simpa [montgomeryReduce_exact_mul] using hNum

theorem montgomeryReduce_range_of_numerator_bounds (a : Int)
    (hlo : 0 ≤ a - montgomeryTruncate a * barrettQ)
    (hhi : a - montgomeryTruncate a * barrettQ < barrettQ * montgomeryModulus) :
    0 ≤ montgomeryReduceInt a ∧ montgomeryReduceInt a < barrettQ := by
  have hmod_nonneg : 0 ≤ montgomeryModulus := by
    native_decide
  have hmod_pos : 0 < montgomeryModulus := by
    native_decide
  constructor
  · simpa [montgomeryReduce_eq_ediv] using
      Int.ediv_nonneg hlo hmod_nonneg
  · simpa [montgomeryReduce_eq_ediv] using
      (Int.ediv_lt_iff_lt_mul hmod_pos).2 hhi

theorem montgomeryReduce_correct (a : Int) : sgenVC (montgomeryReduceSpec a) := by
  intro st hA
  have hEvalA : evalExpr (.var "a") st = some (.int a) := by
    simpa [evalExpr] using hA
  let t₁ := montgomeryTruncate a
  let st₁ := st.updateVar "t" (.int t₁)
  have hEvalTruncate :
      evalExpr montgomeryTruncateExpr st = some (.int t₁) := by
    simp [montgomeryTruncateExpr, evalExpr, evalStaticExpr, hEvalA, t₁,
      montgomeryTruncate, montgomeryQInvAbs, wrapSignedInt, uintModulus,
      evalBinOp_mul_int_int', evalBinOp_sub_int_int']
  have hA₁ : st₁.lookupVar "a" = some (.int a) := by
    calc
      st₁.lookupVar "a" = st.lookupVar "a" := by
        simpa [st₁] using lookupVar_updateVar_ne st "t" "a" (.int t₁) (by decide : "a" ≠ "t")
      _ = some (.int a) := hA
  have hT₁ : st₁.lookupVar "t" = some (.int t₁) := by
    simpa [st₁] using lookupVar_updateVar_eq st "t" (.int t₁)
  let t₂ := montgomeryReduceInt a
  let st₂ := st₁.updateVar "t" (.int t₂)
  have hEvalReduce :
      evalExpr montgomeryReduceExpr st₁ = some (.int t₂) := by
    calc
      evalExpr montgomeryReduceExpr st₁
          = evalBinOp .shr (.int (a - t₁ * barrettQ)) (.int 16) := by
              simp [montgomeryReduceExpr, evalExpr, evalStaticExpr, hA₁, hT₁,
                evalBinOp_mul_int_int', evalBinOp_sub_int_int']
      _ = some (.int t₂) := by
            simpa [t₂, montgomeryReduceInt] using evalBinOp_shr_int_16 (a - t₁ * barrettQ)
  have hT₂ : st₂.lookupVar "t" = some (.int t₂) := by
    simpa [st₂] using lookupVar_updateVar_eq st₁ "t" (.int t₂)
  have hEvalRet :
      evalExpr (.var "t") st₂ = some (.int t₂) := by
    simpa [evalExpr] using hT₂
  have ht₂ : t₂ = montgomeryReduceInt a := by
    rfl
  change swp montgomeryReduceBody (montgomeryReduceSpec a).post st
  simp [montgomeryReduceBody, swp, montgomeryReduceSpec, hEvalTruncate, hEvalReduce, hEvalRet,
    st₁, st₂, ht₂]

end HeytingLean.LeanCP.RealWorld
