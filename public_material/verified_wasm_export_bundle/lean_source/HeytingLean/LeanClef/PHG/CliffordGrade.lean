import HeytingLean.LeanClef.DTS.AbelianGroup

/-!
# LeanClef.PHG.CliffordGrade

Formalize Haynes' Proposition 3.1: "Grade is a DTS dimension axis."

Reference: Haynes arXiv:2603.17627, Section 3.2, Proposition 3.1
-/

namespace LeanClef.PHG

/-- A Clifford algebra Cl(p,q,r) with p+q+r = dim. -/
structure CliffordAlgebra where
  dim : Nat
  sig_p : Nat
  sig_q : Nat
  sig_r : Nat
  sig_valid : sig_p + sig_q + sig_r = dim
  dim_pos : 0 < dim
  deriving DecidableEq

/-- Grade k ∈ {0, ..., dim}. -/
abbrev Grade (cl : CliffordAlgebra) := Fin (cl.dim + 1)

/-- |a - b| as Nat ≤ max(a, b) for natural numbers. -/
private theorem natAbs_sub_le_max (a b : Nat) :
    (a - b : Int).natAbs ≤ max a b := by
  omega

/-- Outer product grade: grade(a ∧ b) = grade(a) + grade(b) if ≤ dim. -/
def outerProductGrade (cl : CliffordAlgebra) (p q : Grade cl) : Option (Grade cl) :=
  let sum := p.val + q.val
  if h : sum ≤ cl.dim then some ⟨sum, by omega⟩ else none

/-- Inner product grade: grade(a · b) = |grade(a) - grade(b)|. -/
def innerProductGrade (cl : CliffordAlgebra) (p q : Grade cl) : Grade cl :=
  ⟨(p.val - q.val : Int).natAbs, by
    have hp := p.isLt
    have hq := q.isLt
    have h := natAbs_sub_le_max p.val q.val
    omega⟩

/-- Geometric product output grades: |p-q|, |p-q|+2, ..., min(p+q, dim). -/
def geometricProductGrades (cl : CliffordAlgebra) (p q : Grade cl) : List (Grade cl) :=
  let lo := (p.val - q.val : Int).natAbs
  let hi := min (p.val + q.val) cl.dim
  (List.range ((hi - lo) / 2 + 1)).filterMap fun i =>
    let g := lo + 2 * i
    if h : g ≤ cl.dim then some ⟨g, by omega⟩ else none

/-- Proposition 3.1: The outer product grade rule is additive. -/
theorem grade_is_additive (cl : CliffordAlgebra) (p q : Grade cl)
    (g : Grade cl) (h : outerProductGrade cl p q = some g) :
    g.val = p.val + q.val := by
  unfold outerProductGrade at h
  by_cases hle : p.val + q.val ≤ cl.dim
  · simp [hle] at h
    exact (congrArg Fin.val h).symm
  · simp [hle] at h

/-- Grade consistency is decidable. -/
instance grade_decidable (cl : CliffordAlgebra) (p q : Grade cl)
    (expected : Grade cl) :
    Decidable (outerProductGrade cl p q = some expected) :=
  inferInstance

/-- The standard PGA algebra Cl(3,0,1). -/
def PGA : CliffordAlgebra := ⟨4, 3, 0, 1, by omega, by omega⟩

end LeanClef.PHG
