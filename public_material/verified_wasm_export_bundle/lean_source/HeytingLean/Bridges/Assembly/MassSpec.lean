import Mathlib.Data.List.Basic
import HeytingLean.ATheory.AssemblyCore

/-
# MassSpec bridge: spectra, fragmentation graph, and MA upper bound

This module provides a minimal, type-correct scaffold for connecting mass
spectrometry data to the Assembly Theory core. It defines:

* a simple peak and spectrum representation;
* a typed fragmentation edge and list-based "graph";
* a trivial MA upper bound function.

The intent is to keep the initial bridge lightweight and fully compiling.
Later phases can extend `fragGraph` and `maUpperBound` with realistic
fragmentation and pathway logic without changing the exported interfaces.
-/

namespace HeytingLean
namespace Bridges
namespace Assembly

open HeytingLean.ATheory

universe u

/-- A single mass-spectrometry peak with mass-to-charge and intensity. -/
structure Peak where
  mz        : ℝ
  intensity : ℝ

/-- A spectrum is a finite list of peaks. -/
structure Spectrum where
  peaks : List Peak

/-- A directed fragmentation edge between assembly objects of type `Obj Nat`.

We index fragments by natural numbers, typically corresponding to positions
in a spectrum or a derived fragment list. -/
structure FragEdge where
  src : Obj Nat
  dst : Obj Nat

/-- A very simple fragmentation graph: just a list of edges over `Obj Nat`.
Later work can replace this with a more structured graph representation. -/
abbrev FragGraph := List FragEdge

/-- Construct a fragmentation graph from a spectrum, under a given numerical
tolerance `δ`. The current implementation ignores `δ` but uses the number
of peaks to build a simple linear chain of fragments represented as
`Obj.base i` for `i = 0, …, n-1`. -/
def fragGraph (_δ : ℝ) (S : Spectrum) : FragGraph :=
  let n := S.peaks.length
  let idxs := List.range n
  -- Build edges i → i+1 as a linear chain.
  (idxs.zip idxs.tail).map (fun ⟨i, j⟩ =>
    { src := Obj.base i, dst := Obj.base j })

/-- A trivial upper bound on molecular assembly index derived from a
fragmentation graph: the number of edges in the constructed chain. -/
def maUpperBound (G : FragGraph) : Nat :=
  G.length

end Assembly
end Bridges
end HeytingLean
