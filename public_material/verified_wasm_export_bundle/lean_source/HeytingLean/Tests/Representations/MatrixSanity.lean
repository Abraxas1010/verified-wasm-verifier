import HeytingLean.Representations.Matrix

/-!
# Sanity: matrix representations

Lightweight compile-time checks for the matrix representation scaffolding.
-/

namespace HeytingLean.Tests.Representations.Matrix

open HeytingLean.Representations.Matrix

section
variable {n : ℕ} {R : Type} [Semiring R]

example (A B : Tensor.TensorElem n R) :
    LensRepr.toMatrix (L := Tensor.TensorElem n R) (n := n) (R := R) (A * B) =
      LensRepr.toMatrix (L := Tensor.TensorElem n R) (n := n) (R := R) A *
        LensRepr.toMatrix (L := Tensor.TensorElem n R) (n := n) (R := R) B := by
  exact LensRepr.toMatrix_mul (L := Tensor.TensorElem n R) (n := n) (R := R) A B

end

section
variable {n : ℕ}

example (G : SimpleGraph (Fin (Nat.succ n))) [DecidableRel G.Adj] :
    Graph.adjacencyMatrix (R := Nat) G (0 : Fin (Nat.succ n)) (0 : Fin (Nat.succ n)) = 0 := by
  exact Graph.adjacencyMatrix_diag (R := Nat) (G := G) (i := (0 : Fin (Nat.succ n)))

end

end HeytingLean.Tests.Representations.Matrix
