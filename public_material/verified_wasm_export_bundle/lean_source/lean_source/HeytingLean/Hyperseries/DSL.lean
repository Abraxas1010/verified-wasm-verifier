import Mathlib.SetTheory.Ordinal.Basic

namespace HeytingLean
namespace Hyperseries

/--
Syntactic hyperseries expression language parameterized by coefficient type.
-/
inductive ExprC (Coeff : Type*) where
  | C : Coeff → ExprC Coeff
  | X : ExprC Coeff
  | add : ExprC Coeff → ExprC Coeff → ExprC Coeff
  | mul : ExprC Coeff → ExprC Coeff → ExprC Coeff
  | neg : ExprC Coeff → ExprC Coeff
  | exp : ExprC Coeff → ExprC Coeff
  | log : ExprC Coeff → ExprC Coeff
  | hyperExp : Ordinal → ExprC Coeff → ExprC Coeff
  | hyperLog : Ordinal → ExprC Coeff → ExprC Coeff
  deriving Inhabited

namespace ExprC

instance {Coeff : Type*} : Add (ExprC Coeff) := ⟨ExprC.add⟩
instance {Coeff : Type*} : Mul (ExprC Coeff) := ⟨ExprC.mul⟩
instance {Coeff : Type*} : Neg (ExprC Coeff) := ⟨ExprC.neg⟩
instance {Coeff : Type*} : Sub (ExprC Coeff) := ⟨fun a b => ExprC.add a (ExprC.neg b)⟩

end ExprC

/-- Integer-coefficient hyperseries expressions (current surreal-compatible lane). -/
abbrev HExpr := ExprC ℤ

/-- Rational-coefficient hyperseries expressions (preferred rich-coefficient lane). -/
abbrev HExprQ := ExprC Rat

namespace HExpr

abbrev C : ℤ → HExpr := @ExprC.C ℤ
abbrev X : HExpr := @ExprC.X ℤ
abbrev add : HExpr → HExpr → HExpr := ExprC.add
abbrev mul : HExpr → HExpr → HExpr := ExprC.mul
abbrev neg : HExpr → HExpr := ExprC.neg
abbrev exp : HExpr → HExpr := ExprC.exp
abbrev log : HExpr → HExpr := ExprC.log
abbrev hyperExp : Ordinal → HExpr → HExpr := ExprC.hyperExp
abbrev hyperLog : Ordinal → HExpr → HExpr := ExprC.hyperLog

end HExpr

namespace HExprQ

abbrev C : Rat → HExprQ := @ExprC.C Rat
abbrev X : HExprQ := @ExprC.X Rat
abbrev add : HExprQ → HExprQ → HExprQ := ExprC.add
abbrev mul : HExprQ → HExprQ → HExprQ := ExprC.mul
abbrev neg : HExprQ → HExprQ := ExprC.neg
abbrev exp : HExprQ → HExprQ := ExprC.exp
abbrev log : HExprQ → HExprQ := ExprC.log
abbrev hyperExp : Ordinal → HExprQ → HExprQ := ExprC.hyperExp
abbrev hyperLog : Ordinal → HExprQ → HExprQ := ExprC.hyperLog

end HExprQ
end Hyperseries
end HeytingLean
