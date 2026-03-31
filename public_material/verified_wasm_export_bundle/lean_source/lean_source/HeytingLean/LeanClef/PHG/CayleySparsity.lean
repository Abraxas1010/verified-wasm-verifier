import HeytingLean.LeanClef.PHG.CliffordGrade

/-!
# LeanClef.PHG.CayleySparsity

Formalize and quantify the sparsity of the geometric product
Cayley table derivable from grade inference alone.

Reference: Haynes arXiv:2603.17627, Section 3.3

The sparsity metric counts grade-level triples: for a d-dimensional
Clifford algebra with grades 0..d, the total number of
(input_grade, input_grade, output_grade) triples is (d+1)^3.
A triple (p, q, g) is "non-zero" if grade g appears in the
geometric product of grade-p and grade-q elements. The sparsity
is the fraction of triples that are structurally zero.
-/

namespace LeanClef.PHG

/-- Binomial coefficient C(n, k) = n! / (k! * (n-k)!). -/
def binomial : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _ + 1 => 0
  | n + 1, k + 1 => binomial n k + binomial n (k + 1)

/-- Basis element count at grade k in d dimensions = C(d, k). -/
def basisCount (d k : Nat) : Nat := binomial d k

/-- Total grade-triple count: (d+1)^3 triples (p, q, g) where
    p, q, g ∈ {0, ..., d}. -/
def gradeTripleCount (d : Nat) : Nat := (d + 1) ^ 3

/-- Count of nonzero grade triples: for each (p, q), count how many
    output grades g appear in geometricProductGrades. -/
def nonzeroGradeTriples (cl : CliffordAlgebra) : Nat :=
  let grades : List (Grade cl) := (List.range (cl.dim + 1)).filterMap fun k =>
    if h : k ≤ cl.dim then some ⟨k, by omega⟩ else none
  grades.foldl (fun acc p =>
    grades.foldl (fun acc' q =>
      acc' + (geometricProductGrades cl p q).length) acc) 0

/-- Sparsity numerator = total triples - nonzero triples.
    Sparsity fraction = sparsityNumer / gradeTripleCount. -/
def sparsityNumer (cl : CliffordAlgebra) : Nat :=
  gradeTripleCount cl.dim - nonzeroGradeTriples cl

/-- PGA grade-triple count: 5^3 = 125. -/
example : gradeTripleCount PGA.dim = 125 := by native_decide

/-- PGA nonzero triples < total triples (sparsity exists). -/
example : nonzeroGradeTriples PGA < gradeTripleCount PGA.dim := by native_decide

/-- PGA sparsity numerator is positive (some triples are structurally zero). -/
example : 0 < sparsityNumer PGA := by native_decide

/-- PGA basis count sanity: C(4,2) = 6 (bivectors). -/
example : basisCount 4 2 = 6 := by native_decide

end LeanClef.PHG
