import Mathlib.Logic.Hydra
import Mathlib.RingTheory.FreeRing
import HeytingLean.Hyperseries.Core
import HeytingLean.Hyperseries.DSL
import HeytingLean.Hyperseries.SurrealExpLogSemantics

set_option linter.deprecated.module false

namespace HeytingLean
namespace Hyperseries

namespace CoreExpr

/--
Phase-1 executable core: free ring on one generator.
This gives a genuine ring-hom evaluation at surreal `ω`.
-/
abbrev Expr : Type := FreeRing Unit

/-- Distinguished variable symbol. -/
def X : Expr := FreeRing.of ()

/-- Evaluate the free variable at `omegaSurreal`. -/
noncomputable def evalOmega : Expr →+* Surreal :=
  FreeRing.lift (fun _ : Unit => omegaSurreal)

@[simp] theorem evalOmega_X : evalOmega X = omegaSurreal := by
  simp [X, evalOmega]

@[simp] theorem evalOmega_int (z : ℤ) : evalOmega (z : Expr) = (z : Surreal) := by
  simp [evalOmega]

end CoreExpr

/--
Conservative surreal model candidate:
`ω` is fixed, and exp/log/hyper-operators are supplied by the active
`SurrealExpLogSemantics` package.
-/
noncomputable abbrev surrealSemantics (useNontrivial : Bool) : SurrealExpLogSemantics :=
  SurrealExpLogSemantics.select useNontrivial

noncomputable abbrev surrealModelWith (useNontrivial : Bool) : HyperserialModel Surreal :=
  SurrealExpLogSemantics.toModel (surrealSemantics useNontrivial)

@[simp] theorem surrealModelWith_eq_toModel (useNontrivial : Bool) :
    surrealModelWith useNontrivial = SurrealExpLogSemantics.toModel (surrealSemantics useNontrivial) := rfl

@[simp] theorem surrealModelWith_omega (useNontrivial : Bool) :
    (surrealModelWith useNontrivial).omega = omegaSurreal := by
  rfl

@[simp] theorem surrealSemantics_false :
    surrealSemantics false = SurrealExpLogSemantics.default := by
  simp [surrealSemantics]

@[simp] theorem surrealSemantics_true :
    surrealSemantics true = SurrealExpLogSemantics.negSemantics := by
  simp [surrealSemantics]

@[simp] theorem surrealModelWith_false :
    surrealModelWith false = SurrealExpLogSemantics.toModel SurrealExpLogSemantics.default := by
  simp [surrealModelWith, surrealSemantics]

@[simp] theorem surrealModelWith_true :
    surrealModelWith true = SurrealExpLogSemantics.toModel SurrealExpLogSemantics.negSemantics := by
  simp [surrealModelWith, surrealSemantics]

@[simp] theorem surrealModelWith_false_exp (x : Surreal) :
    (surrealModelWith false).exp x = x := by
  simp [surrealModelWith, surrealSemantics]

@[simp] theorem surrealModelWith_false_log (x : Surreal) :
    (surrealModelWith false).log x = x := by
  simp [surrealModelWith, surrealSemantics]

@[simp] theorem surrealModelWith_false_hyperExp (α : Ordinal) (x : Surreal) :
    (surrealModelWith false).hyperExp α x = x := by
  simp [surrealModelWith, surrealSemantics]

@[simp] theorem surrealModelWith_false_hyperLog (α : Ordinal) (x : Surreal) :
    (surrealModelWith false).hyperLog α x = x := by
  simp [surrealModelWith, surrealSemantics]

noncomputable abbrev surrealSemanticsDefault : SurrealExpLogSemantics :=
  SurrealExpLogSemantics.active

@[simp] theorem surrealSemanticsDefault_eq_active :
    surrealSemanticsDefault = SurrealExpLogSemantics.active := rfl

noncomputable instance instHyperserialModelSurreal : HyperserialModel Surreal :=
  SurrealExpLogSemantics.toModel surrealSemanticsDefault

/-- Named handle for the default surreal hyperserial model candidate. -/
noncomputable abbrev surrealModel : HyperserialModel Surreal :=
  instHyperserialModelSurreal

@[simp] theorem surrealModel_eq_activeModel :
    surrealModel = SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active := rfl

@[simp] theorem surrealModel_eq_modelWith_false :
    surrealModel = surrealModelWith false := by
  simp [surrealModel, instHyperserialModelSurreal, surrealSemanticsDefault,
    surrealModelWith, surrealSemantics, SurrealExpLogSemantics.active]

@[simp] theorem surrealModel_eq_defaultModel :
    surrealModel = SurrealExpLogSemantics.toModel SurrealExpLogSemantics.default := by
  calc
    surrealModel = surrealModelWith false := surrealModel_eq_modelWith_false
    _ = SurrealExpLogSemantics.toModel SurrealExpLogSemantics.default := surrealModelWith_false

@[simp] theorem surrealModel_eq_placeholderModel :
    surrealModel = SurrealExpLogSemantics.toModel SurrealExpLogSemantics.placeholder := by
  calc
    surrealModel = SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active :=
      surrealModel_eq_activeModel
    _ = SurrealExpLogSemantics.toModel SurrealExpLogSemantics.placeholder :=
      congrArg SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active_eq_placeholder

@[simp] theorem surrealModelWith_true_exp (x : Surreal) :
    HyperserialModel.exp (self := surrealModelWith true) x = -x := by
  simp [surrealModelWith, surrealSemantics]

@[simp] theorem surrealModelWith_true_log (x : Surreal) :
    HyperserialModel.log (self := surrealModelWith true) x = -x := by
  simp [surrealModelWith, surrealSemantics]

@[simp] theorem surrealModelWith_true_hyperExp_zero (x : Surreal) :
    HyperserialModel.hyperExp (self := surrealModelWith true) 0 x = -x := by
  simp [surrealModelWith, surrealSemantics]

@[simp] theorem surrealModelWith_true_hyperLog_zero (x : Surreal) :
    HyperserialModel.hyperLog (self := surrealModelWith true) 0 x = -x := by
  simp [surrealModelWith, surrealSemantics]

@[simp] theorem surrealModelWith_exp_if (useNontrivial : Bool) (x : Surreal) :
    (surrealModelWith useNontrivial).exp x = (if useNontrivial then -x else x) := by
  cases useNontrivial <;> simp [surrealModelWith, surrealSemantics]

@[simp] theorem surrealModelWith_log_if (useNontrivial : Bool) (x : Surreal) :
    (surrealModelWith useNontrivial).log x = (if useNontrivial then -x else x) := by
  cases useNontrivial <;> simp [surrealModelWith, surrealSemantics]

@[simp] theorem surrealModelWith_hyperExp_zero_if (useNontrivial : Bool) (x : Surreal) :
    (surrealModelWith useNontrivial).hyperExp 0 x = (if useNontrivial then -x else x) := by
  cases useNontrivial <;> simp [surrealModelWith, surrealSemantics]

@[simp] theorem surrealModelWith_hyperLog_zero_if (useNontrivial : Bool) (x : Surreal) :
    (surrealModelWith useNontrivial).hyperLog 0 x = (if useNontrivial then -x else x) := by
  cases useNontrivial <;> simp [surrealModelWith, surrealSemantics]

@[simp] theorem surrealModel_omega :
    HyperserialModel.omega (self := surrealModel) = omegaSurreal := by
  rfl

@[simp] theorem surrealModel_exp (x : Surreal) :
    HyperserialModel.exp (self := surrealModel) x = x := by
  rfl

@[simp] theorem surrealModel_log (x : Surreal) :
    HyperserialModel.log (self := surrealModel) x = x := by
  rfl

@[simp] theorem surrealModel_hyperExp (α : Ordinal) (x : Surreal) :
    HyperserialModel.hyperExp (self := surrealModel) α x = x := by
  rfl

@[simp] theorem surrealModel_hyperLog (α : Ordinal) (x : Surreal) :
    HyperserialModel.hyperLog (self := surrealModel) α x = x := by
  rfl

noncomputable instance instHyperserialModelLawsSurreal :
    HyperserialModelLaws Surreal surrealModel := by
  simpa [surrealModel, instHyperserialModelSurreal, surrealSemanticsDefault] using
    (SurrealExpLogSemantics.instModelLaws surrealSemanticsDefault)

namespace HExpr

/-- Interpret `HExpr` inside any `HyperserialModel`. -/
def eval {K : Type*} [CommRing K] (M : HyperserialModel K) : HExpr → K
  | ExprC.C z => (z : K)
  | ExprC.X => M.omega
  | ExprC.add a b => eval M a + eval M b
  | ExprC.mul a b => eval M a * eval M b
  | ExprC.neg a => -eval M a
  | ExprC.exp a => M.exp (eval M a)
  | ExprC.log a => M.log (eval M a)
  | ExprC.hyperExp α a => M.hyperExp α (eval M a)
  | ExprC.hyperLog α a => M.hyperLog α (eval M a)

@[simp] theorem eval_C {K : Type*} [CommRing K] (M : HyperserialModel K) (z : ℤ) :
    eval M (ExprC.C z) = (z : K) := rfl

@[simp] theorem eval_X {K : Type*} [CommRing K] (M : HyperserialModel K) :
    eval M (ExprC.X : HExpr) = M.omega := rfl

@[simp] theorem eval_add {K : Type*} [CommRing K] (M : HyperserialModel K) (a b : HExpr) :
    eval M (ExprC.add a b) = eval M a + eval M b := rfl

@[simp] theorem eval_mul {K : Type*} [CommRing K] (M : HyperserialModel K) (a b : HExpr) :
    eval M (ExprC.mul a b) = eval M a * eval M b := rfl

@[simp] theorem eval_neg {K : Type*} [CommRing K] (M : HyperserialModel K) (a : HExpr) :
    eval M (ExprC.neg a) = -eval M a := rfl

@[simp] theorem eval_sub {K : Type*} [CommRing K] (M : HyperserialModel K) (a b : HExpr) :
    eval M (a - b) = eval M a - eval M b := by
  simp [sub_eq_add_neg, eval]

@[simp] theorem eval_zero {K : Type*} [CommRing K] (M : HyperserialModel K) :
    eval M (ExprC.C (0 : ℤ)) = (0 : K) := by
  simp

@[simp] theorem eval_one {K : Type*} [CommRing K] (M : HyperserialModel K) :
    eval M (ExprC.C (1 : ℤ)) = (1 : K) := by
  simp

theorem eval_add_assoc {K : Type*} [CommRing K] (M : HyperserialModel K) (a b c : HExpr) :
    eval M (ExprC.add (ExprC.add a b) c) = eval M (ExprC.add a (ExprC.add b c)) := by
  simp [add_assoc]

theorem eval_mul_assoc {K : Type*} [CommRing K] (M : HyperserialModel K) (a b c : HExpr) :
    eval M (ExprC.mul (ExprC.mul a b) c) = eval M (ExprC.mul a (ExprC.mul b c)) := by
  simp [mul_assoc]

theorem eval_eq_of_model_eq {K : Type*} [CommRing K]
    {M N : HyperserialModel K} (h : M = N) (e : HExpr) :
    eval M e = eval N e := by
  cases h
  rfl

@[simp] theorem eval_surrealModel_X :
    eval surrealModel (ExprC.X : HExpr) = omegaSurreal := by
  rfl

@[simp] theorem eval_surrealModel_int (z : ℤ) :
    eval surrealModel (ExprC.C z) = (z : Surreal) := by
  simp [eval]

@[simp] theorem eval_surrealModel_eq_modelWith_false (e : HExpr) :
    eval surrealModel e = eval (surrealModelWith false) e := by
  exact eval_eq_of_model_eq surrealModel_eq_modelWith_false e

@[simp] theorem eval_surrealModel_eq_activeModel (e : HExpr) :
    eval surrealModel e =
      eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) e := by
  exact eval_eq_of_model_eq surrealModel_eq_activeModel e

@[simp] theorem eval_surrealModel_eq_defaultModel (e : HExpr) :
    eval surrealModel e =
      eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.default) e := by
  exact eval_eq_of_model_eq surrealModel_eq_defaultModel e

@[simp] theorem eval_surrealModel_eq_placeholderModel (e : HExpr) :
    eval surrealModel e =
      eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.placeholder) e := by
  exact eval_eq_of_model_eq surrealModel_eq_placeholderModel e

@[simp] theorem eval_defaultModel_eq_placeholderModel (e : HExpr) :
    eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.default) e =
      eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.placeholder) e := by
  calc
    eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.default) e = eval surrealModel e := by
      exact (eval_surrealModel_eq_defaultModel e).symm
    _ = eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.placeholder) e := by
      exact eval_surrealModel_eq_placeholderModel e

@[simp] theorem eval_activeModel_eq_defaultModel (e : HExpr) :
    eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) e =
      eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.default) e := by
  calc
    eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) e = eval surrealModel e := by
      exact (eval_surrealModel_eq_activeModel e).symm
    _ = eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.default) e := by
      exact eval_surrealModel_eq_defaultModel e

@[simp] theorem eval_activeModel_eq_placeholderModel (e : HExpr) :
    eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) e =
      eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.placeholder) e := by
  calc
    eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.active) e = eval surrealModel e := by
      exact (eval_surrealModel_eq_activeModel e).symm
    _ = eval (SurrealExpLogSemantics.toModel SurrealExpLogSemantics.placeholder) e := by
      exact eval_surrealModel_eq_placeholderModel e

end HExpr

namespace HExprQ

/-- Interpret `HExprQ` inside any `HyperserialModel`, with rational constants. -/
def eval {K : Type*} [Field K] (M : HyperserialModel K) : HExprQ → K
  | ExprC.C q => (q : K)
  | ExprC.X => M.omega
  | ExprC.add a b => eval M a + eval M b
  | ExprC.mul a b => eval M a * eval M b
  | ExprC.neg a => -eval M a
  | ExprC.exp a => M.exp (eval M a)
  | ExprC.log a => M.log (eval M a)
  | ExprC.hyperExp α a => M.hyperExp α (eval M a)
  | ExprC.hyperLog α a => M.hyperLog α (eval M a)

@[simp] theorem eval_C {K : Type*} [Field K] (M : HyperserialModel K) (q : Rat) :
    eval M (@ExprC.C Rat q) = (q : K) := rfl

@[simp] theorem eval_X {K : Type*} [Field K] (M : HyperserialModel K) :
    eval M ((@ExprC.X Rat) : HExprQ) = M.omega := rfl

@[simp] theorem eval_add {K : Type*} [Field K] (M : HyperserialModel K) (a b : HExprQ) :
    eval M (@ExprC.add Rat a b) = eval M a + eval M b := rfl

@[simp] theorem eval_mul {K : Type*} [Field K] (M : HyperserialModel K) (a b : HExprQ) :
    eval M (@ExprC.mul Rat a b) = eval M a * eval M b := rfl

@[simp] theorem eval_neg {K : Type*} [Field K] (M : HyperserialModel K) (a : HExprQ) :
    eval M (@ExprC.neg Rat a) = -eval M a := rfl

@[simp] theorem eval_sub {K : Type*} [Field K] (M : HyperserialModel K) (a b : HExprQ) :
    eval M (a - b) = eval M a - eval M b := by
  simp [sub_eq_add_neg, eval]

@[simp] theorem eval_zero {K : Type*} [Field K] (M : HyperserialModel K) :
    eval M (@ExprC.C Rat (0 : Rat)) = (0 : K) := by
  simp

@[simp] theorem eval_one {K : Type*} [Field K] (M : HyperserialModel K) :
    eval M (@ExprC.C Rat (1 : Rat)) = (1 : K) := by
  simp

@[simp] theorem eval_intCast {K : Type*} [Field K] (M : HyperserialModel K) (z : ℤ) :
    eval M (@ExprC.C Rat (z : Rat)) = (z : K) := by
  simp

@[simp] theorem eval_natCast {K : Type*} [Field K] (M : HyperserialModel K) (n : ℕ) :
    eval M (@ExprC.C Rat (n : Rat)) = (n : K) := by
  simp

theorem eval_add_assoc {K : Type*} [Field K] (M : HyperserialModel K) (a b c : HExprQ) :
    eval M (ExprC.add (ExprC.add a b) c) = eval M (ExprC.add a (ExprC.add b c)) := by
  simp [add_assoc]

theorem eval_mul_assoc {K : Type*} [Field K] (M : HyperserialModel K) (a b c : HExprQ) :
    eval M (ExprC.mul (ExprC.mul a b) c) = eval M (ExprC.mul a (ExprC.mul b c)) := by
  simp [mul_assoc]

theorem eval_eq_of_model_eq {K : Type*} [Field K]
    {M N : HyperserialModel K} (h : M = N) (e : HExprQ) :
    eval M e = eval N e := by
  cases h
  rfl

end HExprQ

end Hyperseries
end HeytingLean
