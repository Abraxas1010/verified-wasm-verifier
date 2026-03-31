import HeytingLean.CCI.Core
import HeytingLean.CCI.Json
import HeytingLean.CCI.Cert

open HeytingLean.CCI

/-!
# CCI JSON encode/hash smoke tests (Lean-side)

We currently provide string encoders only; these tests check that encoders
produce non-empty strings and that `hashExpr` is stable across invocations.
-/

-- Expression encode + hash stability
#eval do
  let e1 := Expr.atom "a"
  let e2 := Expr.andR (Expr.atom "a") (Expr.atom "b")
  let e3 := Expr.impR (Expr.notR (Expr.atom "x")) (Expr.orR (Expr.atom "y") (Expr.atom "z"))
  let e4 :=
    Expr.lam "x" .default (.const "Nat" [])
      (.app (.const "Nat.succ" []) (.bvar 0))
  let e5 :=
    Expr.forallE "α" .implicit (.sort (.succ .zero))
      (.const "Sort" [.zero])
  let ss := [encodeExprStr e1, encodeExprStr e2, encodeExprStr e3, encodeExprStr e4, encodeExprStr e5]
  let encOk := ss.all (fun s => s.length > 0)
  let h1 := hashExpr e1
  let h2 := hashExpr e2
  let h3 := hashExpr e3
  let h4 := hashExpr e4
  let h5 := hashExpr e5
  let hashStable := (h1 = hashExpr e1) && (h2 = hashExpr e2) && (h3 = hashExpr e3) &&
    (h4 = hashExpr e4) && (h5 = hashExpr e5)
  let roundtripOk :=
    match decodeExprStr (encodeExprStr e4), decodeExprStr (encodeExprStr e5) with
    | some e4', some e5' => e4' = e4 && e5' = e5
    | _, _ => false
  IO.println s!"cci-json-encode: {encOk}"
  IO.println s!"cci-hash-stability: {hashStable}"
  IO.println s!"cci-roundtrip-rich: {roundtripOk}"

-- Lens encode smoke
#eval do
  let l : Lens := { name := "geo", value := "opaque" }
  let s := encodeLensStr l
  IO.println s!"cci-lens-encode-nonempty: {decide (s.length > 0)}"
