import HeytingLean.CCI.Core
import HeytingLean.CCI.Cert
import HeytingLean.CCI.Check

open HeytingLean.CCI

/-!
# CCI Checker tests (compile‑only via #eval)

Positive: correct digest for omega. Negative: tampered digest.
-/

#eval do
  let omega := Expr.impR (Expr.atom "P") (Expr.atom "Q")
  let rewrites : List Nat := []
  let d := hashExpr (canon omega)
  let cert : Certificate := { inputs := [], omega := omega, lensImgs := [], rewrites := rewrites, digests := [("omega", d)] }
  IO.println s!"cci-check-positive: {check cert}"

#eval do
  let omega := Expr.impR (Expr.atom "P") (Expr.atom "Q")
  let rewrites : List Nat := []
  let wrong := ByteArray.mk #[0x00, 0x01]
  let cert : Certificate := { inputs := [], omega := omega, lensImgs := [], rewrites := rewrites, digests := [("omega", wrong)] }
  IO.println s!"cci-check-negative: {check cert}"

#eval do
  let omega := Expr.impR (Expr.atom "P") (Expr.atom "Q")
  let hImp := hashExpr omega
  let hCanon := hashExpr (canon omega)
  let eq : Bool := decide (hImp = hCanon)
  IO.println s!"cci-hash-imp-vs-canon-equal: {eq}"

#eval do
  let e := Expr.andR (Expr.atom "a") (Expr.andR (Expr.atom "b") (Expr.atom "a"))
  let c1 := canon e
  let c2 := canon c1
  let idem : Bool := decide (c1 = c2)
  IO.println s!"cci-canon-idempotent: {idem}"

#eval do
  let omega :=
    Expr.lam "x" .default (.const "Nat" [])
      (.app (.const "Nat.succ" []) (.bvar 0))
  let d := hashExpr (canon omega)
  let cert : Certificate :=
    { inputs := [], omega := omega, lensImgs := [], rewrites := [], digests := [("omega", d)] }
  IO.println s!"cci-check-rich-structural: {check cert}"
