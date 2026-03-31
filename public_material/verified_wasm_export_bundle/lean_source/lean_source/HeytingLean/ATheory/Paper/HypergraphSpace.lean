import HeytingLean.ATheory.Paper.AssemblyIndex

namespace HeytingLean
namespace ATheory
namespace Paper

/-!
# Extension 3: Assembly as hyperpaths in B-hypergraphs

Flamm–Merkle–Stadler (2025) observe that assembly pathways can be identified with
minimal hyperpaths in a directed **B-hypergraph** (a directed hypergraph whose
hyperarcs have exactly one output vertex).

This file makes that connection precise in our paper-facing API:

* A B-hypergraph is exactly the same shape of data as `AssemblySpace` (`V`, `U`, `E`).
* A sequential hyperpath with reuse is exactly `AssemblySpace.AssemblyPath`.
* The minimal hyperpath length is exactly `AssemblySpace.AssemblyIndex.assemblyIndex`.

We package the hypergraph view as a thin wrapper so downstream code can phrase
results in hypergraph terminology without duplicating the existing path/index
infrastructure.
-/

namespace BHypergraph

universe u

 /-- A directed B-hypergraph with binary sources and a single target.

`E x y z` is a directed hyperarc with sources `x,y` and (unique) output `z`.
The set `U` is the set of primitives / initially available vertices.
-/
structure Graph where
  V : Type u
  U : Set V
  E : V → V → V → Prop

/-- View a B-hypergraph as a paper-facing `AssemblySpace`. -/
def toAssemblySpace (H : Graph) : AssemblySpace where
  Ω := H.V
  U := H.U
  J := H.E

/-- A hyperedge packaged with evidence it is allowed (same data as `AssemblySpace.Step`). -/
abbrev Edge (H : Graph) := AssemblySpace.Step (S := toAssemblySpace H)

/-- A reuse-capable sequential hyperpath for `z` (definitional alias of `AssemblyPath`). -/
abbrev HyperPath (H : Graph) (z : H.V) :=
  AssemblySpace.AssemblyPath (S := toAssemblySpace H) z

abbrev Closed (H : Graph) : Prop := AssemblySpace.Closed (toAssemblySpace H)

namespace HyperIndex

/-- A vertex `z` has a hyperpath of length `n`. -/
def HasHyperPathLen (H : Graph) (z : H.V) (n : Nat) : Prop :=
  ∃ p : HyperPath H z, p.len = n

/-- The minimal hyperpath length (hypergraph view of `AssemblyIndex.assemblyIndex`). -/
noncomputable def hyperIndex (H : Graph) (hC : Closed H) (z : H.V) : Nat :=
  AssemblySpace.AssemblyIndex.assemblyIndex (S := toAssemblySpace H) (hC := hC) z

lemma hyperIndex_spec (H : Graph) (hC : Closed H) (z : H.V) :
    HasHyperPathLen H z (hyperIndex H hC z) := by
  rcases AssemblySpace.AssemblyIndex.assemblyIndex_spec (S := toAssemblySpace H) hC z with ⟨p, hp⟩
  exact ⟨p, hp⟩

lemma hyperIndex_le_of_hasLen (H : Graph) (hC : Closed H) (z : H.V) {n : Nat}
    (hn : HasHyperPathLen H z n) :
    hyperIndex H hC z ≤ n := by
  rcases hn with ⟨p, hp⟩
  have :
      AssemblySpace.AssemblyIndex.assemblyIndex (S := toAssemblySpace H) (hC := hC) z ≤ n := by
    exact AssemblySpace.AssemblyIndex.assemblyIndex_le_of_hasLen (S := toAssemblySpace H) hC z ⟨p, hp⟩
  simpa [hyperIndex] using this

lemma hyperIndex_le_of_path (H : Graph) (hC : Closed H) {z : H.V} (p : HyperPath H z) :
    hyperIndex H hC z ≤ p.len := by
  simpa [hyperIndex] using
    (AssemblySpace.AssemblyIndex.assemblyIndex_le_of_path (S := toAssemblySpace H) hC p)

end HyperIndex

/-! ## Induced B-hypergraph from an `AssemblySpace` -/

/-- Forget the name "assembly space" and view the join predicate as a B-hyperedge relation. -/
def ofAssemblySpace (S : AssemblySpace) : Graph where
  V := S.Ω
  U := S.U
  E := S.J

@[simp] lemma toAssemblySpace_ofAssemblySpace (S : AssemblySpace) :
    toAssemblySpace (ofAssemblySpace S) = S := rfl

namespace HyperIndex

@[simp] lemma hyperIndex_ofAssemblySpace_eq (S : AssemblySpace) (hC : AssemblySpace.Closed S) (z : S.Ω) :
    hyperIndex (H := ofAssemblySpace S) (hC := by simpa using hC) z =
      AssemblySpace.AssemblyIndex.assemblyIndex (S := S) (hC := hC) z := rfl

end HyperIndex

end BHypergraph

end Paper
end ATheory
end HeytingLean
