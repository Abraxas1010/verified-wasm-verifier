import HeytingLean.ATP.DifferentiableATP.CategoricalBridge
import HeytingLean.ATP.DifferentiableATP.CoreOps
import HeytingLean.Embeddings.Adelic

/-!
# ATP.DifferentiableATP.SheafResolution

Multi-scale lens resolution for differentiable ATP.

- each lens has a basis + resolution level,
- coarse/fine restriction maps are explicit,
- per-lens retracts are non-trivial (basis + nucleus projection).
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

open HeytingLean.Embeddings
open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential
open HeytingLean.LoF.Combinators.Differential.Compute

structure LensScale where
  lens : LensID
  basis : List Comb
  resolution : Nat
  deriving Repr

def lensScale : LensID → LensScale
  | .omega =>
      {
        lens := .omega
        basis := [.K, .S, .Y, .app .S .K, .app .K .S, .app .Y .K]
        resolution := 5
      }
  | .tensor =>
      {
        lens := .tensor
        basis := [.K, .S, .Y, .app .K .S]
        resolution := 4
      }
  | .graph =>
      {
        lens := .graph
        basis := [.K, .S, .Y, .app .S .K]
        resolution := 3
      }
  | .clifford =>
      {
        lens := .clifford
        basis := [.K, .S, .app .S .K]
        resolution := 2
      }
  | .topology =>
      {
        lens := .topology
        basis := [.K, .S, .Y]
        resolution := 2
      }
  | .region =>
      {
        lens := .region
        basis := [.K, .S]
        resolution := 1
      }
  | .matula =>
      {
        lens := .matula
        basis := [.K, .S, .Y, .app .S .K, .app .K .S]
        resolution := 4
      }

def basisForLens (lens : LensID) : List Comb :=
  (lensScale lens).basis

def resolutionForLens (lens : LensID) : Nat :=
  (lensScale lens).resolution

def basisSizeForLens (lens : LensID) : Nat :=
  (basisForLens lens).length

def projectToBasis (basis : List Comb) (w : FSum) : FSum :=
  w.filter (fun tc => tc.1 ∈ basis)

theorem mem_projectToBasis {basis : List Comb} {w : FSum} {tc : Comb × Rat} :
    tc ∈ projectToBasis basis w ↔ tc ∈ w ∧ tc.1 ∈ basis := by
  simp [projectToBasis, List.mem_filter]

theorem projectToBasis_idempotent (basis : List Comb) (w : FSum) :
    projectToBasis basis (projectToBasis basis w) = projectToBasis basis w := by
  unfold projectToBasis
  simp [List.filter_filter]

theorem projectToBasis_compose_of_subset
    (fine coarse : List Comb)
    (w : FSum)
    (hsubset : ∀ c, c ∈ coarse → c ∈ fine) :
    projectToBasis coarse (projectToBasis fine w) = projectToBasis coarse w := by
  induction w with
  | nil =>
      simp [projectToBasis]
  | cons hd tl ih =>
      rcases hd with ⟨t, c⟩
      have ih' :
          List.filter (fun a => decide (a.1 ∈ coarse) && decide (a.1 ∈ fine)) tl =
            List.filter (fun tc => decide (tc.1 ∈ coarse)) tl := by
        simpa [projectToBasis, List.filter_filter, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc] using ih
      by_cases hCoarse : t ∈ coarse
      · have hFine : t ∈ fine := hsubset t hCoarse
        simp [projectToBasis, hCoarse, hFine, ih']
      · simp [projectToBasis, hCoarse, ih']

theorem projectToBasis_commutes_with_fixed (basis : List Comb) (w : FSum) :
    projectToBasis basis (projectToFixedWeights nucleusR w) =
      projectToFixedWeights nucleusR (projectToBasis basis w) := by
  unfold projectToBasis projectToFixedWeights
  simp [List.filter_filter, Bool.and_comm]

def lensProjection (lens : LensID) (w : FSum) : FSum :=
  projectToBasis (basisForLens lens) w

theorem lensProjection_idempotent (lens : LensID) (w : FSum) :
    lensProjection lens (lensProjection lens w) = lensProjection lens w := by
  simpa [lensProjection] using projectToBasis_idempotent (basisForLens lens) w

def lensRetractWeights (lens : LensID) (w : FSum) : FSum :=
  lensProjection lens (projectToFixedWeights nucleusR w)

theorem lensRetractWeights_idempotent (lens : LensID) (w : FSum) :
    lensRetractWeights lens (lensRetractWeights lens w) = lensRetractWeights lens w := by
  unfold lensRetractWeights lensProjection
  calc
    projectToBasis (basisForLens lens)
        (projectToFixedWeights nucleusR
          (projectToBasis (basisForLens lens) (projectToFixedWeights nucleusR w)))
      =
      projectToFixedWeights nucleusR
        (projectToBasis (basisForLens lens)
          (projectToBasis (basisForLens lens) (projectToFixedWeights nucleusR w))) := by
            simpa using
              (projectToBasis_commutes_with_fixed
                (basisForLens lens)
                (projectToBasis (basisForLens lens) (projectToFixedWeights nucleusR w)))
    _ =
      projectToFixedWeights nucleusR
        (projectToBasis (basisForLens lens) (projectToFixedWeights nucleusR w)) := by
          rw [projectToBasis_idempotent (basisForLens lens) (projectToFixedWeights nucleusR w)]
    _ =
      projectToBasis (basisForLens lens) (projectToFixedWeights nucleusR (projectToFixedWeights nucleusR w)) := by
          symm
          simpa using
            (projectToBasis_commutes_with_fixed
              (basisForLens lens)
              (projectToFixedWeights nucleusR w))
    _ = projectToBasis (basisForLens lens) (projectToFixedWeights nucleusR w) := by
          rw [projectToFixedWeights_idempotent nucleusR w]

def lensRetract (lens : LensID) : IdempotentRetract FSum where
  R := lensRetractWeights lens
  idempotent := lensRetractWeights_idempotent lens

def basisSubset (fine coarse : LensID) : Prop :=
  ∀ c, c ∈ basisForLens coarse → c ∈ basisForLens fine

theorem basisSubset_refl (lens : LensID) : basisSubset lens lens := by
  intro c hc
  exact hc

theorem basisSubset_trans {a b c : LensID}
    (hab : basisSubset a b)
    (hbc : basisSubset b c) :
    basisSubset a c := by
  intro t ht
  exact hab t (hbc t ht)

theorem omega_subset_tensor : basisSubset .omega .tensor := by
  intro c hc
  simp [basisForLens, lensScale] at hc ⊢
  rcases hc with hK | hS | hY | hKS
  · exact Or.inl hK
  · exact Or.inr (Or.inl hS)
  · exact Or.inr (Or.inr (Or.inl hY))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hKS))))

theorem omega_subset_graph : basisSubset .omega .graph := by
  intro c hc
  simp [basisForLens, lensScale] at hc ⊢
  rcases hc with hK | hS | hY | hSK
  · exact Or.inl hK
  · exact Or.inr (Or.inl hS)
  · exact Or.inr (Or.inr (Or.inl hY))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hSK)))

theorem matula_subset_graph : basisSubset .matula .graph := by
  intro c hc
  simp [basisForLens, lensScale] at hc ⊢
  rcases hc with hK | hS | hY | hSK
  · exact Or.inl hK
  · exact Or.inr (Or.inl hS)
  · exact Or.inr (Or.inr (Or.inl hY))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hSK)))

theorem matula_subset_tensor : basisSubset .matula .tensor := by
  intro c hc
  simp [basisForLens, lensScale] at hc ⊢
  rcases hc with hK | hS | hY | hKS
  · exact Or.inl hK
  · exact Or.inr (Or.inl hS)
  · exact Or.inr (Or.inr (Or.inl hY))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hKS)))

theorem omega_subset_matula : basisSubset .omega .matula := by
  intro c hc
  simp [basisForLens, lensScale] at hc ⊢
  rcases hc with hK | hS | hY | hSK | hKS
  · exact Or.inl hK
  · exact Or.inr (Or.inl hS)
  · exact Or.inr (Or.inr (Or.inl hY))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hSK)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hKS))))

theorem not_basisSubset_graph_matula : ¬ basisSubset .graph .matula := by
  intro h
  have hKS : .app .K .S ∈ basisForLens .matula := by
    simp [basisForLens, lensScale]
  have hInGraph : .app .K .S ∈ basisForLens .graph := h (.app .K .S) hKS
  simp [basisForLens, lensScale] at hInGraph

theorem tensor_subset_topology : basisSubset .tensor .topology := by
  intro c hc
  simp [basisForLens, lensScale] at hc ⊢
  rcases hc with hK | hS | hY
  · exact Or.inl hK
  · exact Or.inr (Or.inl hS)
  · exact Or.inr (Or.inr (Or.inl hY))

theorem graph_subset_topology : basisSubset .graph .topology := by
  intro c hc
  simp [basisForLens, lensScale] at hc ⊢
  rcases hc with hK | hS | hY
  · exact Or.inl hK
  · exact Or.inr (Or.inl hS)
  · exact Or.inr (Or.inr (Or.inl hY))

theorem matula_subset_topology : basisSubset .matula .topology := by
  intro c hc
  simp [basisForLens, lensScale] at hc ⊢
  rcases hc with hK | hS | hY
  · exact Or.inl hK
  · exact Or.inr (Or.inl hS)
  · exact Or.inr (Or.inr (Or.inl hY))

theorem graph_subset_clifford : basisSubset .graph .clifford := by
  intro c hc
  simp [basisForLens, lensScale] at hc ⊢
  rcases hc with hK | hS | hSK
  · exact Or.inl hK
  · exact Or.inr (Or.inl hS)
  · exact Or.inr (Or.inr (Or.inr hSK))

theorem topology_subset_region : basisSubset .topology .region := by
  intro c hc
  simp [basisForLens, lensScale] at hc ⊢
  rcases hc with hK | hS
  · exact Or.inl hK
  · exact Or.inr (Or.inl hS)

theorem clifford_subset_region : basisSubset .clifford .region := by
  intro c hc
  simp [basisForLens, lensScale] at hc ⊢
  rcases hc with hK | hS
  · exact Or.inl hK
  · exact Or.inr (Or.inl hS)

theorem omega_subset_topology : basisSubset .omega .topology :=
  basisSubset_trans omega_subset_tensor tensor_subset_topology

theorem omega_subset_clifford : basisSubset .omega .clifford :=
  basisSubset_trans omega_subset_graph graph_subset_clifford

theorem tensor_subset_region : basisSubset .tensor .region :=
  basisSubset_trans tensor_subset_topology topology_subset_region

theorem graph_subset_region : basisSubset .graph .region :=
  basisSubset_trans graph_subset_topology topology_subset_region

theorem omega_subset_region : basisSubset .omega .region :=
  basisSubset_trans omega_subset_topology topology_subset_region

theorem matula_subset_region : basisSubset .matula .region :=
  basisSubset_trans matula_subset_topology topology_subset_region

theorem not_basisSubset_graph_tensor : ¬ basisSubset .graph .tensor := by
  intro h
  have hKS : .app .K .S ∈ basisForLens .tensor := by
    simp [basisForLens, lensScale]
  have hInGraph : .app .K .S ∈ basisForLens .graph := h (.app .K .S) hKS
  simp [basisForLens, lensScale] at hInGraph

theorem not_basisSubset_tensor_graph : ¬ basisSubset .tensor .graph := by
  intro h
  have hSK : .app .S .K ∈ basisForLens .graph := by
    simp [basisForLens, lensScale]
  have hInTensor : .app .S .K ∈ basisForLens .tensor := h (.app .S .K) hSK
  simp [basisForLens, lensScale] at hInTensor

theorem graph_tensor_incomparable :
    ¬ basisSubset .graph .tensor ∧ ¬ basisSubset .tensor .graph := by
  exact ⟨not_basisSubset_graph_tensor, not_basisSubset_tensor_graph⟩

theorem not_basisSubset_clifford_topology : ¬ basisSubset .clifford .topology := by
  intro h
  have hY : .Y ∈ basisForLens .topology := by
    simp [basisForLens, lensScale]
  have hInClifford : .Y ∈ basisForLens .clifford := h .Y hY
  simp [basisForLens, lensScale] at hInClifford

theorem not_basisSubset_topology_clifford : ¬ basisSubset .topology .clifford := by
  intro h
  have hSK : .app .S .K ∈ basisForLens .clifford := by
    simp [basisForLens, lensScale]
  have hInTopology : .app .S .K ∈ basisForLens .topology := h (.app .S .K) hSK
  simp [basisForLens, lensScale] at hInTopology

theorem clifford_topology_incomparable :
    ¬ basisSubset .clifford .topology ∧ ¬ basisSubset .topology .clifford := by
  exact ⟨not_basisSubset_clifford_topology, not_basisSubset_topology_clifford⟩

theorem resolution_monotone_of_basisSubset {fine coarse : LensID}
    (hsubset : basisSubset fine coarse) :
    resolutionForLens fine ≥ resolutionForLens coarse := by
  cases fine <;> cases coarse <;>
    simp [basisSubset, basisForLens, lensScale, resolutionForLens] at hsubset ⊢

theorem sheaf_restriction_commutes
    (fine coarse : LensID)
    (w : FSum)
    (hsubset : basisSubset fine coarse) :
    projectToBasis (basisForLens coarse) (lensRetractWeights fine w) =
      lensRetractWeights coarse (projectToBasis (basisForLens coarse) w) := by
  have hLeft :
      projectToBasis (basisForLens coarse) (lensRetractWeights fine w) =
        projectToBasis (basisForLens coarse) (projectToFixedWeights nucleusR w) := by
    unfold lensRetractWeights lensProjection
    exact projectToBasis_compose_of_subset
      (fine := basisForLens fine)
      (coarse := basisForLens coarse)
      (w := projectToFixedWeights nucleusR w)
      hsubset
  have hRight :
      lensRetractWeights coarse (projectToBasis (basisForLens coarse) w) =
        projectToBasis (basisForLens coarse) (projectToFixedWeights nucleusR w) := by
    unfold lensRetractWeights lensProjection
    have hComm :=
      (projectToBasis_commutes_with_fixed (basisForLens coarse) w).symm
    calc
      projectToBasis (basisForLens coarse)
          (projectToFixedWeights nucleusR (projectToBasis (basisForLens coarse) w))
          =
          projectToBasis (basisForLens coarse)
            (projectToBasis (basisForLens coarse) (projectToFixedWeights nucleusR w)) := by
              rw [hComm]
      _ = projectToBasis (basisForLens coarse) (projectToFixedWeights nucleusR w) := by
            simpa using
              projectToBasis_idempotent
                (basisForLens coarse)
                (projectToFixedWeights nucleusR w)
  exact hLeft.trans hRight.symm

theorem region_subset_all (fine : LensID) :
    basisSubset fine .region := by
  intro c hc
  have hRegion : c = .K ∨ c = .S := by
    simpa [basisForLens, lensScale] using hc
  rcases hRegion with hK | hS
  · subst hK
    cases fine <;> simp [basisForLens, lensScale]
  · subst hS
    cases fine <;> simp [basisForLens, lensScale]

end DifferentiableATP
end ATP
end HeytingLean
