import Mathlib.Logic.Hydra
import Mathlib.SetTheory.Surreal.Basic
import HeytingLean.Hyperseries.Description
import HeytingLean.Hyperseries.Eval

set_option linter.deprecated.module false

namespace HeytingLean
namespace Hyperseries

/--
Staged canonical-description codes for surreal hyperseries.

`literal` keeps total coverage over `Surreal`; `expr` records DSL witnesses.
-/
inductive SurrealDescCode where
  | literal : Surreal → SurrealDescCode
  | expr : HExpr → SurrealDescCode

/-- Semantic realization of staged surreal-description codes. -/
noncomputable def SurrealDescCode.realize : SurrealDescCode → Surreal
  | .literal a => a
  | .expr e => HExpr.eval surrealModel e

namespace SurrealDescCode

@[simp] theorem realize_literal (a : Surreal) :
    realize (.literal a) = a := rfl

@[simp] theorem realize_expr (e : HExpr) :
    realize (.expr e) = HExpr.eval surrealModel e := rfl

end SurrealDescCode

/-- Two staged codes are equivalent exactly when they realize to the same surreal value. -/
def SurrealDescRel (x y : SurrealDescCode) : Prop :=
  SurrealDescCode.realize x = SurrealDescCode.realize y

/-- Setoid implementing semantic quotienting of staged surreal-description codes. -/
def surrealDescSetoid : Setoid SurrealDescCode where
  r := SurrealDescRel
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      rfl
    · intro x y h
      exact h.symm
    · intro x y z hxy hyz
      exact Eq.trans hxy hyz

/--
Non-test hyperserial description instance for surreals.

This replaces the old identity carrier with a semantic quotient of staged
description codes, while retaining full existence/uniqueness guarantees.
-/
noncomputable instance instHyperserialDescriptionSurreal : HyperserialDescription Surreal where
  HS := Quotient surrealDescSetoid
  describe := fun a => Quotient.mk surrealDescSetoid (SurrealDescCode.literal a)
  realize := Quotient.lift SurrealDescCode.realize (by
    intro x y hxy
    exact hxy)
  realize_describe := by
    intro a
    rfl
  describe_realize := by
    intro h
    refine Quotient.inductionOn h ?_
    intro c
    exact Quotient.sound rfl

/-- Stage an expression as a canonical surreal-description code class. -/
noncomputable def describeExprCode (e : HExpr) : HDesc Surreal :=
  Quotient.mk surrealDescSetoid (SurrealDescCode.expr e)

@[simp] theorem eval_describeExprCode (e : HExpr) :
    HyperserialDescription.realize (K := Surreal) (describeExprCode e) =
      HExpr.eval surrealModel e := by
  rfl

theorem describe_eval_eq_describeExprCode (e : HExpr) :
    HyperserialDescription.describe (K := Surreal) (HExpr.eval surrealModel e) =
      describeExprCode e := by
  exact Quotient.sound rfl

end Hyperseries
end HeytingLean
