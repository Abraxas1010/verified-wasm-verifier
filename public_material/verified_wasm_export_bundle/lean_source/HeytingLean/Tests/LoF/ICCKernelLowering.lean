import Lean
import HeytingLean.LoF.ICCKernel.Faithfulness

namespace HeytingLean
namespace Tests
namespace LoF
namespace ICCKernelLowering

open HeytingLean.LoF.ICCKernel
open HeytingLean.LoF.ICCKernel.Lower

def sampleExpr : Lean.Expr :=
  Lean.Expr.forallE `x (.sort .zero) (.bvar 0) .default

def sampleLetExpr : Lean.Expr :=
  Lean.Expr.letE `x (.sort .zero) (.sort .zero) (.bvar 0) true

example : ∃ t, lowerExpr sampleExpr = .ok t := by
  exact lowerExpr_total sampleExpr

example : ∀ t, lowerExpr sampleExpr = .ok t → Term.containsFallbackMarker t = false := by
  exact lowerExpr_output_has_no_fallback_marker sampleExpr

def sampleSyntax : Lean.Syntax :=
  Lean.Syntax.ident Lean.SourceInfo.none "foo".toSubstring `foo []

run_cmd do
  let rendered := reprStr (lowerMetaValue (.ofSyntax sampleSyntax))
  let expected :=
    "HeytingLean.LoF.ICCKernel.MetaValue.syntax\n" ++
    "  (HeytingLean.LoF.ICCKernel.SyntaxView.ident\n" ++
    "    (HeytingLean.LoF.ICCKernel.SourceInfoView.none)\n" ++
    "    { source := \"foo\", text := \"foo\", startByte := 0, stopByte := 3 }\n" ++
    "    (HeytingLean.LoF.ICCKernel.Name.str (HeytingLean.LoF.ICCKernel.Name.anonymous) \"foo\")\n" ++
    "    [])"
  unless rendered = expected do
    throwError s!"unexpected lowered syntax metadata:\n{rendered}"

example : Raise.raiseTerm (Lower.lowerExprCore sampleExpr) = .ok sampleExpr := by
  exact Raise.raiseTerm_lowerExprCore sampleExpr

example : Raise.raiseTerm (Lower.lowerExprCore sampleLetExpr) = .ok sampleLetExpr := by
  exact Raise.raiseTerm_lowerExprCore sampleLetExpr

example :
    recoverAndRelowerExpr (Lower.lowerExprCore sampleExpr) = .ok (Lower.lowerExprCore sampleExpr) := by
  exact recoverAndRelower_lowerExprCore_roundTrip sampleExpr

example :
    recoverAndRelowerExpr (Lower.lowerExprCore sampleLetExpr) = .ok (Lower.lowerExprCore sampleLetExpr) := by
  exact recoverAndRelower_lowerExprCore_roundTrip sampleLetExpr

end ICCKernelLowering
end LoF
end Tests
end HeytingLean
