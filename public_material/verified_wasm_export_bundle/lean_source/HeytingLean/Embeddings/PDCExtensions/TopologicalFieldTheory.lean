import HeytingLean.Embeddings.PerspectivalDescentHierarchy

/-!
# Embeddings.PDCExtensions.TopologicalFieldTheory

Family I representatives:
- extended TQFT codimension views
- factorization-algebra open-set views
- Floer flavor views
-/

namespace HeytingLean
namespace Embeddings
namespace PDCExtensions

/-! ## I1: Extended TQFT perspectives -/

inductive CodimLevel where
  | c0 | c1 | c2 | c3
  deriving DecidableEq, Repr, Inhabited

instance : Fintype CodimLevel where
  elems := {.c0, .c1, .c2, .c3}
  complete t := by cases t <;> simp

def codimAsNat : CodimLevel → Nat
  | .c0 => 0
  | .c1 => 1
  | .c2 => 2
  | .c3 => 3

instance extendedTQFTPDC :
    PDCWithDescent CodimLevel (fun _ => Int) where
  integral _ := {x | x = 0}
  finiteness x := by
    exact Set.toFinite {t : CodimLevel | x t ≠ 0}
  truncate t k x := if codimAsNat t ≤ k then x else 0
  Plato := Int
  toPlato _ x := x
  fromPlato _ p := p
  rt1 _ _ := rfl
  rt2 _ _ := rfl
  MatchingFamily x := ∀ t, x t = x .c0
  amalgamate x hx := ⟨x .c0, by intro t; exact (hx t).symm⟩

theorem tqft_c3_truncates_to_zero_below3 (k : Nat) (hk : k < 3) (x : Int) :
    PerspectivalDescentCarrier.truncate
      (τ := CodimLevel) (Carrier := fun _ => Int) .c3 k x = 0 := by
  by_cases hle : codimAsNat .c3 ≤ k
  · exact (False.elim (Nat.not_le_of_lt hk hle))
  · have hle3 : ¬ (3 ≤ k) := by simpa [codimAsNat] using hle
    simp [PerspectivalDescentCarrier.truncate, codimAsNat, hle3]

/-! ## I2: Factorization-algebra open-set perspectives -/

inductive SpacetimeOpen where
  | u0 | u1 | u2
  deriving DecidableEq, Repr, Inhabited

instance : Fintype SpacetimeOpen where
  elems := {.u0, .u1, .u2}
  complete t := by cases t <;> simp

instance factorizationPDC :
    PDCWithDescent SpacetimeOpen (fun _ => Int) where
  integral _ := {x | x = 0}
  finiteness x := by
    exact Set.toFinite {t : SpacetimeOpen | x t ≠ 0}
  truncate _ k x := if k = 0 then 0 else x
  Plato := Int
  toPlato _ x := x
  fromPlato _ p := p
  rt1 _ _ := rfl
  rt2 _ _ := rfl
  MatchingFamily x := ∀ t, x t = x .u0
  amalgamate x hx := ⟨x .u0, by intro t; exact (hx t).symm⟩

theorem factorization_truncate_zero (U : SpacetimeOpen) (x : Int) :
    PerspectivalDescentCarrier.truncate
      (τ := SpacetimeOpen) (Carrier := fun _ => Int) U 0 x = 0 := by
  simp [PerspectivalDescentCarrier.truncate]

/-! ## I3: Floer flavor perspectives -/

inductive FloerFlavor where
  | lagrangian | heegaard | instanton | monopole | ech
  deriving DecidableEq, Repr, Inhabited

instance : Fintype FloerFlavor where
  elems := {.lagrangian, .heegaard, .instanton, .monopole, .ech}
  complete t := by cases t <;> simp

instance floerPDC :
    PDCWithDescent FloerFlavor (fun _ => Int) where
  integral _ := {x | x = 0}
  finiteness x := by
    exact Set.toFinite {t : FloerFlavor | x t ≠ 0}
  truncate _ k x := x % Int.ofNat (k + 1)
  Plato := Int
  toPlato _ x := x
  fromPlato _ p := p
  rt1 _ _ := rfl
  rt2 _ _ := rfl
  MatchingFamily x := ∀ t, x t = x .lagrangian
  amalgamate x hx := ⟨x .lagrangian, by intro t; exact (hx t).symm⟩

theorem floer_forward_cocycle :
    PDCWithTransport.ForwardCocycle
      (τ := FloerFlavor) (Carrier := fun _ => Int) := by
  simpa using
    (PDCWithTransport.forward_is_cocycle
      (τ := FloerFlavor) (Carrier := fun _ => Int))

end PDCExtensions
end Embeddings
end HeytingLean
