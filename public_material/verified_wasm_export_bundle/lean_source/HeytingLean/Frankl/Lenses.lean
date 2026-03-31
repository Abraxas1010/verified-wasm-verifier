import HeytingLean.Frankl.Defs
import HeytingLean.Embeddings.CoreLenses
import HeytingLean.Embeddings.Adelic

/-
- source_type: combinatorics / representation theory
- attribution_status: n/a (lens infrastructure)
- claim_status: n/a
- proof_status: proved
-/

namespace HeytingLean
namespace Frankl
namespace Lenses

open HeytingLean.Embeddings

/-- Graph lens representation of a union-closed family. -/
structure GraphView (α : Type*) [DecidableEq α] where
  vertices : Finset α
  edges : Finset (Finset α)
  edgeSubset : ∀ e ∈ edges, e ⊆ vertices
  unionClosed : Frankl.UnionClosed edges

/-- Lattice/FCA lens representation of a union-closed family. -/
structure LatticeView (α : Type*) [DecidableEq α] where
  elements : Finset (Finset α)
  joinClosed : ∀ A B, A ∈ elements → B ∈ elements → A ∪ B ∈ elements
  joinIrreducibles : Finset (Finset α)
  jiSubset : joinIrreducibles ⊆ elements

/-- Information-theory (entropy/probability) lens representation. -/
structure EntropyView (α : Type*) [DecidableEq α] [Fintype α] where
  family : Finset (Finset α)
  unionClosed : Frankl.UnionClosed family
  uniformProb : α → Rat
  probDef : ∀ x, uniformProb x = (family.filter (fun S => x ∈ S)).card / family.card

/-- Topology lens representation. -/
structure TopologyView (α : Type*) [DecidableEq α] where
  elements : Finset α
  family : Finset (Finset α)
  eulerChar : Int
  betti : List Nat

/-- Tropical lens representation. -/
structure TropicalView (α : Type*) [DecidableEq α] where
  family : Finset (Finset α)
  freqPoly : α → Nat
  freqIsFrankl : freqPoly = Frankl.frequency family

/-- Convert a union-closed family to the graph view. -/
def toGraphView {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (huc : Frankl.UnionClosed F) :
    GraphView α where
  vertices := Frankl.groundSet F
  edges := F
  edgeSubset := by
    intro e he x hx
    exact Finset.mem_biUnion.mpr ⟨e, he, hx⟩
  unionClosed := huc

/-- Convert a union-closed family to the entropy view. -/
def toEntropyView {α : Type*} [DecidableEq α] [Fintype α]
    (F : Finset (Finset α)) (huc : Frankl.UnionClosed F) (_hne : F.Nonempty) :
    EntropyView α where
  family := F
  unionClosed := huc
  uniformProb := fun x => (F.filter (fun S => x ∈ S)).card / F.card
  probDef := by
    intro x
    rfl

/-- Graph and entropy views are consistent on the underlying family. -/
theorem graph_entropy_consistent {α : Type*} [DecidableEq α] [Fintype α]
    (F : Finset (Finset α)) (huc : Frankl.UnionClosed F) (hne : F.Nonempty) :
    (toGraphView F huc).edges = (toEntropyView F huc hne).family := rfl

/-- Entropy-lens formulation of Frankl abundance. -/
theorem frankl_entropy_equiv {α : Type*} [DecidableEq α] [Fintype α]
    (F : Finset (Finset α)) (huc : Frankl.UnionClosed F) (hne : F.Nonempty)
    (hnotempty : ∃ S ∈ F, S.Nonempty) :
    (∃ x, Frankl.Abundant F x) ↔
    ∃ x,
      2 * ((toEntropyView F huc hne).family.filter (fun S => x ∈ S)).card ≥
        (toEntropyView F huc hne).family.card := by
  let _ := hnotempty
  simp [Frankl.Abundant, Frankl.frequency, toEntropyView]

end Lenses
end Frankl
end HeytingLean
