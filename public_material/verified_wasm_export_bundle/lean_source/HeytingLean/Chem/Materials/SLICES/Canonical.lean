import HeytingLean.Chem.Materials.SLICES.Codec
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.String.Basic

/-!
# SLICES: canonicalization and invariance (Phase 3)

The SLICES paper emphasizes invariance under re-orderings. At the combinatorial layer, the core
symmetry is *renaming of node indices* (permuting the unit-cell atom order).

This file defines a canonical SLICES encoding for a labeled quotient graph:

- `canonEncode g` is the **lexicographically minimal** SLICES string among all node permutations.

This yields a stable, permutation-invariant representation that downstream tools can use as a
canonical "key" for a crystal.
-/

namespace HeytingLean.Chem.Materials.SLICES

open scoped Classical

noncomputable def candidateEncodings {n : Nat} (g : LabeledQuotientGraph n) : Finset String :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).image (fun π => encode (g.permute π))

theorem candidateEncodings_nonempty {n : Nat} (g : LabeledQuotientGraph n) :
    (candidateEncodings g).Nonempty := by
  classical
  refine Finset.image_nonempty.2 ?_
  exact (Finset.univ_nonempty : (Finset.univ : Finset (Equiv.Perm (Fin n))).Nonempty)

noncomputable def canonEncode {n : Nat} (g : LabeledQuotientGraph n) : String :=
  (candidateEncodings g).min' (candidateEncodings_nonempty g)

theorem canonEncode_le_encode_permute {n : Nat} (g : LabeledQuotientGraph n) (π : Equiv.Perm (Fin n)) :
    canonEncode g ≤ encode (g.permute π) := by
  classical
  unfold canonEncode
  apply Finset.min'_le
  exact Finset.mem_image.2 ⟨π, by simp, rfl⟩

theorem candidateEncodings_permute {n : Nat} (g : LabeledQuotientGraph n) (σ : Equiv.Perm (Fin n)) :
    candidateEncodings (g.permute σ) = candidateEncodings g := by
  classical
  ext s
  constructor <;> intro hs
  · rcases Finset.mem_image.1 hs with ⟨π, hπ, rfl⟩
    -- (g.permute σ).permute π = g.permute (π * σ)
    have hmul : (g.permute σ).permute π = g.permute (π * σ) := by
      exact LabeledQuotientGraph.permute_mul g σ π
    -- Show membership using the permuted index.
    refine Finset.mem_image.2 ?_
    refine ⟨π * σ, by simp, by simp [hmul]⟩
  · rcases Finset.mem_image.1 hs with ⟨π, hπ, rfl⟩
    -- Choose π' := π * σ⁻¹ so that π = π' * σ.
    let π' : Equiv.Perm (Fin n) := π * σ⁻¹
    have hrew : (g.permute σ).permute π' = g.permute π := by
      -- (g.permute σ).permute (π * σ⁻¹) = g.permute ((π * σ⁻¹) * σ) = g.permute π
      calc
        (g.permute σ).permute π' = g.permute (π' * σ) := by
          exact LabeledQuotientGraph.permute_mul g σ π'
        _ = g.permute π := by
          simp [π', mul_assoc]
    refine Finset.mem_image.2 ?_
    refine ⟨π', by simp [π'], by simp [hrew]⟩

theorem canonEncode_permute {n : Nat} (g : LabeledQuotientGraph n) (σ : Equiv.Perm (Fin n)) :
    canonEncode (g.permute σ) = canonEncode g := by
  classical
  unfold canonEncode
  -- Rewrite the candidate sets; `min'` is definitional once the finsets agree.
  simp [candidateEncodings_permute (g := g) (σ := σ)]

end HeytingLean.Chem.Materials.SLICES
