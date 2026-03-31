import HeytingLean.LeanCP.RealWorld.CtEqVerified
import HeytingLean.LeanCP.Core.VarLemmas
import HeytingLean.LeanCP.VCG.SWPSound
import Mathlib.Tactic

namespace HeytingLean.LeanCP.RealWorld

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

/-- ML-KEM modulus. -/
def barrettQ : Int := 3329

/-- Standard PQClean Barrett constant `⌊(2^26 + q/2)/q⌋`. -/
def barrettV : Int := 20159

def barrettScale : Int := Int.shiftLeft 1 26

def barrettRoundConst : Int := Int.shiftLeft 1 25

def barrettQuotient (a : Int) : Int :=
  Int.shiftRight (barrettV * a + barrettRoundConst) 26

def barrettReduceInt (a : Int) : Int :=
  a - barrettQuotient a * barrettQ

def barrettRoundExpr : CExpr :=
  .binop .shr
    (.binop .add
      (.binop .mul (.intLit barrettV) (.var "a"))
      (.intLit barrettRoundConst))
    (.intLit 26)

def barrettReduceBody : CStmt :=
  .seq
    (.assign (.var "t") barrettRoundExpr)
    (.seq
      (.assign (.var "t") (.binop .mul (.var "t") (.intLit barrettQ)))
      (.ret (.binop .sub (.var "a") (.var "t"))))

def barrettReduceSpec (a : Int) : SFunSpec where
  name := "barrett_reduce"
  params := [("a", .int)]
  retType := .int
  pre := fun st => st.lookupVar "a" = some (.int a)
  post := fun ret _ => ret = .int (barrettReduceInt a)
  body := barrettReduceBody

theorem barrettReduce_noBranch : NoBranch barrettReduceBody := by
  simp [NoBranch, barrettReduceBody]

theorem barrettReduce_congruent (a : Int) :
    barrettReduceInt a % barrettQ = a % barrettQ := by
  unfold barrettReduceInt
  rw [Int.sub_emod, Int.mul_comm, Int.mul_emod_right]
  simp [barrettQ]

private theorem shiftRight_26_eq_ediv (a : Int) :
    Int.shiftRight a 26 = a / barrettScale := by
  have hscale : barrettScale = 67108864 := by
    native_decide
  cases a using Int.rec with
  | ofNat n =>
      rw [hscale]
      simp [Int.shiftRight, Nat.shiftRight_eq_div_pow]
  | negSucc n =>
      rw [hscale, Int.shiftRight, Int.negSucc_eq, Int.negSucc_eq]
      omega

theorem barrettQuotient_eq_ediv (a : Int) :
    barrettQuotient a = (barrettV * a + barrettRoundConst) / barrettScale := by
  simpa [barrettQuotient] using shiftRight_26_eq_ediv (barrettV * a + barrettRoundConst)

theorem barrettReduce_eq_sub_ediv_mul (a : Int) :
    barrettReduceInt a =
      a - ((barrettV * a + barrettRoundConst) / barrettScale) * barrettQ := by
  simp [barrettReduceInt, barrettQuotient_eq_ediv]

/-- On the centered Kyber band, the Barrett quotient stays zero. -/
theorem barrettQuotient_eq_zero_of_abs_le_center (a : Int)
    (hlo : -1664 ≤ a) (hhi : a ≤ 1664) :
    barrettQuotient a = 0 := by
  have hv_nonneg : 0 ≤ barrettV := by
    native_decide
  have hscale_pos : 0 < barrettScale := by
    native_decide
  have hnum_nonneg_const : 0 ≤ barrettV * (-1664 : Int) + barrettRoundConst := by
    native_decide
  have hnum_lt_scale_const : barrettV * (1664 : Int) + barrettRoundConst < barrettScale := by
    native_decide
  have hmul_lower : barrettV * (-1664 : Int) ≤ barrettV * a := by
    exact Int.mul_le_mul_of_nonneg_left hlo hv_nonneg
  have hmul_upper : barrettV * a ≤ barrettV * (1664 : Int) := by
    exact Int.mul_le_mul_of_nonneg_left hhi hv_nonneg
  have hnum_nonneg : 0 ≤ barrettV * a + barrettRoundConst := by
    omega
  have hnum_lt_scale : barrettV * a + barrettRoundConst < barrettScale := by
    exact lt_of_le_of_lt (by omega) hnum_lt_scale_const
  have hq_nonneg : 0 ≤ barrettQuotient a := by
    rw [barrettQuotient_eq_ediv]
    exact Int.ediv_nonneg hnum_nonneg hscale_pos.le
  have hq_lt_one : barrettQuotient a < 1 := by
    rw [barrettQuotient_eq_ediv]
    exact (Int.ediv_lt_iff_lt_mul hscale_pos).2 hnum_lt_scale
  omega

/-- On the centered Kyber band, Barrett reduction is the identity. -/
theorem barrettReduce_eq_self_of_abs_le_center (a : Int)
    (hlo : -1664 ≤ a) (hhi : a ≤ 1664) :
    barrettReduceInt a = a := by
  have hq : barrettQuotient a = 0 := barrettQuotient_eq_zero_of_abs_le_center a hlo hhi
  simp [barrettReduceInt, hq]

private theorem evalBinOp_mul_int_int' (a b : Int) :
    evalBinOp .mul (.int a) (.int b) = some (.int (a * b)) := by
  rfl

private theorem evalBinOp_add_int_int' (a b : Int) :
    evalBinOp .add (.int a) (.int b) = some (.int (a + b)) := by
  rfl

private theorem evalBinOp_shr_int_26 (a : Int) :
    evalBinOp .shr (.int a) (.int 26) = some (.int (Int.shiftRight a 26)) := by
  rfl

private theorem evalBinOp_sub_int_int' (a b : Int) :
    evalBinOp .sub (.int a) (.int b) = some (.int (a - b)) := by
  rfl

theorem barrettReduce_correct (a : Int) : sgenVC (barrettReduceSpec a) := by
  intro st hA
  have hEvalA : evalExpr (.var "a") st = some (.int a) := by
    simpa [evalExpr] using hA
  let t₁ := barrettQuotient a
  let st₁ := st.updateVar "t" (.int t₁)
  have hEvalRound :
      evalExpr barrettRoundExpr st = some (.int t₁) := by
    simp [barrettRoundExpr, evalExpr, evalStaticExpr, hEvalA, t₁, barrettQuotient, barrettRoundConst,
      evalBinOp_mul_int_int', evalBinOp_shr_int_26]
  have hA₁ : st₁.lookupVar "a" = some (.int a) := by
    calc
      st₁.lookupVar "a" = st.lookupVar "a" := by
        simpa [st₁] using lookupVar_updateVar_ne st "t" "a" (.int t₁) (by decide : "a" ≠ "t")
      _ = some (.int a) := hA
  have hT₁ : st₁.lookupVar "t" = some (.int t₁) := by
    simpa [st₁] using lookupVar_updateVar_eq st "t" (.int t₁)
  let t₂ := t₁ * barrettQ
  let st₂ := st₁.updateVar "t" (.int t₂)
  have hEvalScale :
      evalExpr (.binop .mul (.var "t") (.intLit barrettQ)) st₁ = some (.int t₂) := by
    calc
      evalExpr (.binop .mul (.var "t") (.intLit barrettQ)) st₁
          = evalBinOp .mul (.int t₁) (.int barrettQ) := by
              simp [evalExpr, evalStaticExpr, hT₁]
      _ = some (.int t₂) := by
            simpa [t₂] using evalBinOp_mul_int_int' t₁ barrettQ
  have hA₂ : st₂.lookupVar "a" = some (.int a) := by
    calc
      st₂.lookupVar "a" = st₁.lookupVar "a" := by
        simpa [st₂] using lookupVar_updateVar_ne st₁ "t" "a" (.int t₂) (by decide : "a" ≠ "t")
      _ = some (.int a) := hA₁
  have hT₂ : st₂.lookupVar "t" = some (.int t₂) := by
    simpa [st₂] using lookupVar_updateVar_eq st₁ "t" (.int t₂)
  have hEvalRet :
      evalExpr (.binop .sub (.var "a") (.var "t")) st₂ = some (.int (barrettReduceInt a)) := by
    calc
      evalExpr (.binop .sub (.var "a") (.var "t")) st₂
          = evalBinOp .sub (.int a) (.int t₂) := by
              simp [evalExpr, evalStaticExpr, hA₂, hT₂]
      _ = some (.int (barrettReduceInt a)) := by
            simpa [barrettReduceInt, t₁, t₂] using evalBinOp_sub_int_int' a t₂
  change swp barrettReduceBody (barrettReduceSpec a).post st
  simp [barrettReduceBody, swp, barrettReduceSpec, hEvalRound, hEvalScale, hEvalRet, st₁, st₂]

end HeytingLean.LeanCP.RealWorld
