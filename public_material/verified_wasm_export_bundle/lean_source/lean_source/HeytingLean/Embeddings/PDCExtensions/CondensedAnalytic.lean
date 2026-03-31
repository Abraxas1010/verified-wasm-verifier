import HeytingLean.Embeddings.PerspectivalDescentHierarchy

/-!
# Embeddings.PDCExtensions.CondensedAnalytic

Family H representatives:
- condensed test-object perspectives
- liquid-style norm-constrained perspectives
-/

namespace HeytingLean
namespace Embeddings
namespace PDCExtensions

inductive CondensedTestObj where
  | one | cantor2 | cantor4 | profinite8
  deriving DecidableEq, Repr, Inhabited

instance : Fintype CondensedTestObj where
  elems := {.one, .cantor2, .cantor4, .profinite8}
  complete t := by cases t <;> simp

/-! ## H1: Condensed perspectives -/

instance condensedPDC :
    PDCWithDescent CondensedTestObj (fun _ => Int) where
  integral _ := {x | x = 0}
  finiteness x := by
    exact Set.toFinite {t : CondensedTestObj | x t ≠ 0}
  truncate _ k x := x % Int.ofNat (k + 1)
  Plato := Int
  toPlato _ x := x
  fromPlato _ p := p
  rt1 _ _ := rfl
  rt2 _ _ := rfl
  MatchingFamily x := ∀ t, x t = x .one
  amalgamate x hx := ⟨x .one, by intro t; exact (hx t).symm⟩

theorem condensed_truncate_zero (t : CondensedTestObj) (x : Int) :
    PerspectivalDescentCarrier.truncate
      (τ := CondensedTestObj) (Carrier := fun _ => Int) t 0 x = 0 := by
  simp [PerspectivalDescentCarrier.truncate]

/-! ## H2: Liquid-style norm-constrained perspectives -/

structure LiquidValue where
  val : Int
  norm : Nat
  deriving DecidableEq, Repr

instance liquidPDC :
    PDCWithDescent CondensedTestObj (fun _ => LiquidValue) where
  integral _ := {x | x.norm = 0}
  finiteness x := by
    exact Set.toFinite {t : CondensedTestObj | (x t).norm ≠ 0}
  truncate _ k x := { x with norm := Nat.min x.norm k }
  Plato := LiquidValue
  toPlato _ x := x
  fromPlato _ p := p
  rt1 _ _ := rfl
  rt2 _ _ := rfl
  MatchingFamily x := ∀ t, x t = x .one
  amalgamate x hx := ⟨x .one, by intro t; exact (hx t).symm⟩

theorem liquid_truncate_norm_le (t : CondensedTestObj) (k : Nat) (x : LiquidValue) :
    (PerspectivalDescentCarrier.truncate
      (τ := CondensedTestObj) (Carrier := fun _ => LiquidValue) t k x).norm ≤ k := by
  simp [PerspectivalDescentCarrier.truncate]

end PDCExtensions
end Embeddings
end HeytingLean
