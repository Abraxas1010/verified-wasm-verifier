import HeytingLean.Bridges.Graph
import HeytingLean.Bridges.Clifford
import HeytingLean.Quantum.StabilizerNucleus

/-!
# Bridges.EulerBoundaryStabilizer

Wrap existing Euler-boundary bridge encodings into `StabilizerCode` objects so the
stabilizer-nucleus pipeline can consume them directly.
-/

namespace HeytingLean
namespace Bridges
namespace EulerBoundaryStabilizer

open Quantum
open Quantum.StabilizerCode

universe u

section GraphBridge

variable {α : Type u} [LoF.PrimaryAlgebra α]

/-- Euler-boundary wrapper as a single-constraint stabilizer code on graph carriers. -/
def graphEulerBoundaryCode (M : Graph.Model α) : StabilizerCode α :=
  StabilizerCode.ofCodeSpace {x | x = M.R.primordial}

@[simp] theorem graphEulerBoundary_codeSpace (M : Graph.Model α) :
    (graphEulerBoundaryCode M).codeSpace = {x | x = M.R.primordial} := by
  simp [graphEulerBoundaryCode]

theorem graph_encode_eulerBoundary_mem_codeSpace (M : Graph.Model α) :
    M.encode M.R.eulerBoundary ∈ (graphEulerBoundaryCode M).codeSpace := by
  simpa [graphEulerBoundaryCode] using (Graph.Model.encode_eulerBoundary (M := M))

end GraphBridge

section CliffordBridge

variable {α : Type u} [LoF.PrimaryAlgebra α]

/-- Euler-boundary wrapper as a two-constraint stabilizer code on Clifford pair carriers. -/
def cliffordEulerBoundaryCode (M : Clifford.Model α) :
    StabilizerCode (Clifford.Pair α) where
  Gen := Bool
  good := fun
    | true => {p | p.fst = M.R.primordial}
    | false => {p | p.snd = M.R.primordial}

theorem clifford_encode_eulerBoundary_mem_codeSpace (M : Clifford.Model α) :
    M.encode M.R.eulerBoundary ∈ (cliffordEulerBoundaryCode M).codeSpace := by
  intro g
  cases g with
  | false =>
      simpa [cliffordEulerBoundaryCode] using (Clifford.Model.encode_eulerBoundary_snd (M := M))
  | true =>
      simpa [cliffordEulerBoundaryCode] using (Clifford.Model.encode_eulerBoundary_fst (M := M))

end CliffordBridge

end EulerBoundaryStabilizer
end Bridges
end HeytingLean
