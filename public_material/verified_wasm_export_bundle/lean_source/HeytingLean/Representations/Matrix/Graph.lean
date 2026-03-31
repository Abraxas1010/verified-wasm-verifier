import Mathlib.Combinatorics.SimpleGraph.Finite

import HeytingLean.Representations.Matrix.Core

/-!
# Graph lens: adjacency/degree/Laplacian matrices

This module provides small, executable helpers for turning finite graphs into matrices.
-/

namespace HeytingLean
namespace Representations
namespace Matrix
namespace Graph

variable {n : ℕ} {R : Type} [Semiring R]

/-- Adjacency matrix of a simple graph. -/
def adjacencyMatrix (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if G.Adj i j then 1 else 0

@[simp] theorem adjacencyMatrix_apply (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i j : Fin n) :
    adjacencyMatrix (R := R) G i j = (if G.Adj i j then 1 else 0) := by
  simp [adjacencyMatrix]

@[simp] theorem adjacencyMatrix_diag (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (i : Fin n) :
    adjacencyMatrix (R := R) G i i = 0 := by
  simp [adjacencyMatrix]

/-- Degree matrix (diagonal). -/
def degreeMatrix (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal fun i => (G.neighborFinset i).card

end Graph
end Matrix
end Representations
end HeytingLean
