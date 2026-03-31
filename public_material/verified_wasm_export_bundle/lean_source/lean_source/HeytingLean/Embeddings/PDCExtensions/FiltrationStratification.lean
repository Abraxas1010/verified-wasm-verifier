import HeytingLean.Embeddings.PerspectivalDescentHierarchy

/-!
# Embeddings.PDCExtensions.FiltrationStratification

Family F representatives:
- mixed Hodge-style bi-filtration
- perverse/recollement stratification
- chromatic tower levels
-/

namespace HeytingLean
namespace Embeddings
namespace PDCExtensions

/-! ## F1: Mixed Hodge-style bi-filtration -/

inductive MixedHodgePerspective where
  | w0p0 | w0p1 | w1p0 | w1p1
  deriving DecidableEq, Repr, Inhabited

instance : Fintype MixedHodgePerspective where
  elems := {.w0p0, .w0p1, .w1p0, .w1p1}
  complete t := by cases t <;> simp

def mixedWeight : MixedHodgePerspective → Nat
  | .w0p0 | .w0p1 => 0
  | .w1p0 | .w1p1 => 1

instance mixedHodgePDC :
    PDCWithDescent MixedHodgePerspective (fun _ => Int) where
  integral _ := {x | x = 0}
  finiteness x := by
    exact Set.toFinite {t : MixedHodgePerspective | x t ≠ 0}
  truncate t k x := if mixedWeight t ≤ k then x else 0
  Plato := Int
  toPlato _ x := x
  fromPlato _ p := p
  rt1 _ _ := rfl
  rt2 _ _ := rfl
  MatchingFamily x := ∀ t, x t = x .w0p0
  amalgamate x hx := ⟨x .w0p0, by intro t; exact (hx t).symm⟩

theorem mixed_hodge_truncate_zero_of_lt (t : MixedHodgePerspective) (k : Nat)
    (h : k < mixedWeight t) (x : Int) :
    PerspectivalDescentCarrier.truncate
      (τ := MixedHodgePerspective) (Carrier := fun _ => Int) t k x = 0 := by
  by_cases hle : mixedWeight t ≤ k
  · exact (False.elim (Nat.not_le_of_lt h hle))
  · simp [PerspectivalDescentCarrier.truncate, hle]

/-! ## F2: Perverse/recollement stratification -/

inductive PerverseStratum where
  | openStratum | middleStratum | closedStratum
  deriving DecidableEq, Repr, Inhabited

instance : Fintype PerverseStratum where
  elems := {.openStratum, .middleStratum, .closedStratum}
  complete t := by cases t <;> simp

def stratumDepth : PerverseStratum → Nat
  | .openStratum => 0
  | .middleStratum => 1
  | .closedStratum => 2

instance perversePDC :
    PDCWithDescent PerverseStratum (fun _ => Int) where
  integral _ := {x | x = 0}
  finiteness x := by
    exact Set.toFinite {t : PerverseStratum | x t ≠ 0}
  truncate t k x := if stratumDepth t ≤ k then x else 0
  Plato := Int
  toPlato _ x := x
  fromPlato _ p := p
  rt1 _ _ := rfl
  rt2 _ _ := rfl
  MatchingFamily x := ∀ t, x t = x .openStratum
  amalgamate x hx := ⟨x .openStratum, by intro t; exact (hx t).symm⟩

theorem perverse_closed_truncates_to_zero_at_level0 (x : Int) :
    PerspectivalDescentCarrier.truncate
      (τ := PerverseStratum) (Carrier := fun _ => Int)
      .closedStratum 0 x = 0 := by
  simp [PerspectivalDescentCarrier.truncate, stratumDepth]

/-! ## F3: Chromatic tower levels -/

inductive ChromaticHeight where
  | h0 | h1 | h2 | h3
  deriving DecidableEq, Repr, Inhabited

instance : Fintype ChromaticHeight where
  elems := {.h0, .h1, .h2, .h3}
  complete t := by cases t <;> simp

def chromaticLevel : ChromaticHeight → Nat
  | .h0 => 0
  | .h1 => 1
  | .h2 => 2
  | .h3 => 3

instance chromaticPDC :
    PDCWithDescent ChromaticHeight (fun _ => Int) where
  integral _ := {x | x = 0}
  finiteness x := by
    exact Set.toFinite {t : ChromaticHeight | x t ≠ 0}
  truncate t k x := if chromaticLevel t ≤ k then x else 0
  Plato := Int
  toPlato _ x := x
  fromPlato _ p := p
  rt1 _ _ := rfl
  rt2 _ _ := rfl
  MatchingFamily x := ∀ t, x t = x .h0
  amalgamate x hx := ⟨x .h0, by intro t; exact (hx t).symm⟩

theorem chromatic_h3_truncates_to_zero_below_3 (k : Nat) (hk : k < 3) (x : Int) :
    PerspectivalDescentCarrier.truncate
      (τ := ChromaticHeight) (Carrier := fun _ => Int) .h3 k x = 0 := by
  by_cases hle : chromaticLevel .h3 ≤ k
  · exact (False.elim (Nat.not_le_of_lt hk hle))
  · have hle3 : ¬ (3 ≤ k) := by simpa [chromaticLevel] using hle
    simp [PerspectivalDescentCarrier.truncate, chromaticLevel, hle3]

end PDCExtensions
end Embeddings
end HeytingLean
