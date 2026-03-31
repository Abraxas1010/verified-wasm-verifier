import Lean
import HeytingLean.CCI.LeanExpr
import HeytingLean.CCI.Json

open Lean
open HeytingLean.CCI

/-!
# CCI Lean-expression bridge tests

These are structural tests: they ensure the richer CCI carrier can represent
real Lean syntax, not that the lightweight CCI checker proves Lean semantics.
-/

#eval do
  let expr : Lean.Expr :=
    .lam `x (.const ``Nat []) (.app (.const ``Nat.succ []) (.bvar 0)) .default
  let lowered := HeytingLean.CCI.ofExpr expr
  let expected :=
    Expr.lam "x" .default (.const "Nat" [])
      (.app (.const "Nat.succ" []) (.bvar 0))
  IO.println s!"cci-ofExpr-lam: {decide (lowered = expected)}"

#eval do
  let expr : Lean.Expr :=
    .forallE `α (.sort (.succ .zero))
      (.forallE `x (.bvar 0) (.app (.const ``List []) (.bvar 0)) .default)
      .implicit
  let lowered := HeytingLean.CCI.ofExpr expr
  let roundtripOk :=
    match decodeExprStr (encodeExprStr lowered) with
    | some lowered' => decide (lowered' = lowered)
    | none => false
  IO.println s!"cci-ofExpr-roundtrip: {roundtripOk}"
