import HeytingLean.Numbers.SurrealCore
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Heyting.Boundary
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Set.Lattice

namespace HeytingLean
namespace Numbers
namespace Surreal

open HeytingLean.Numbers.SurrealCore

/-- Boundary/co-negation operations over a Bi-Heyting carrier. -/
structure BoundaryOps (α : Type _) [BiheytingAlgebra α] where
  coNeg : α → α
  boundary : α → α
  boundary_eq_inf_coNeg : ∀ a : α, boundary a = a ⊓ coNeg a

namespace BoundaryOps

variable {α : Type _} [BiheytingAlgebra α] (ops : BoundaryOps α)

/-- Boundary-driven "nonexistent" classification. -/
def nonExistent (a : α) : Prop := ops.boundary a = ⊥

/-- Boundary-driven "impossible" classification. -/
def impossible (a : α) : Prop := ops.boundary a ≠ ⊥

@[simp] theorem boundary_apply (a : α) : ops.boundary a = ops.boundary a := rfl

@[simp] theorem boundary_eq_inf_coNeg_apply (a : α) :
    ops.boundary a = a ⊓ ops.coNeg a :=
  ops.boundary_eq_inf_coNeg a

@[simp] theorem impossible_iff_not_nonExistent (a : α) :
    ops.impossible a ↔ ¬ ops.nonExistent a := by
  rfl

end BoundaryOps

/-- Canonical boundary operator package on any Bi-Heyting algebra. -/
def canonicalBoundaryOps (α : Type _) [BiheytingAlgebra α] : BoundaryOps α where
  coNeg := fun a => ￢a
  boundary := fun a => Coheyting.boundary a
  boundary_eq_inf_coNeg := by
    intro a
    rfl

@[simp] theorem canonical_boundary_bot (α : Type _) [BiheytingAlgebra α] :
    (canonicalBoundaryOps (α := α)).boundary (⊥ : α) = ⊥ := by
  change Coheyting.boundary (⊥ : α) = ⊥
  exact Coheyting.boundary_bot

@[simp] theorem canonical_boundary_top (α : Type _) [BiheytingAlgebra α] :
    (canonicalBoundaryOps (α := α)).boundary (⊤ : α) = ⊥ := by
  change Coheyting.boundary (⊤ : α) = ⊥
  exact Coheyting.boundary_top

@[simp] theorem canonical_boundary_idem {α : Type _} [BiheytingAlgebra α] (a : α) :
    (canonicalBoundaryOps (α := α)).boundary
      ((canonicalBoundaryOps (α := α)).boundary a) =
      (canonicalBoundaryOps (α := α)).boundary a := by
  change Coheyting.boundary (Coheyting.boundary a) = Coheyting.boundary a
  exact Coheyting.boundary_idem a

theorem canonical_boundary_inf {α : Type _} [BiheytingAlgebra α] (a b : α) :
    (canonicalBoundaryOps (α := α)).boundary (a ⊓ b) =
      ((canonicalBoundaryOps (α := α)).boundary a ⊓ b) ⊔
        (a ⊓ (canonicalBoundaryOps (α := α)).boundary b) := by
  change Coheyting.boundary (a ⊓ b) =
    Coheyting.boundary a ⊓ b ⊔ a ⊓ Coheyting.boundary b
  exact Coheyting.boundary_inf a b

theorem canonical_boundary_sup_le {α : Type _} [BiheytingAlgebra α] (a b : α) :
    (canonicalBoundaryOps (α := α)).boundary (a ⊔ b) ≤
      (canonicalBoundaryOps (α := α)).boundary a ⊔
        (canonicalBoundaryOps (α := α)).boundary b := by
  change Coheyting.boundary (a ⊔ b) ≤ Coheyting.boundary a ⊔ Coheyting.boundary b
  exact Coheyting.boundary_sup_le (a := a) (b := b)

theorem canonical_nonExistent_inf
    {α : Type _} [BiheytingAlgebra α] (a b : α)
    (ha : (canonicalBoundaryOps (α := α)).nonExistent a)
    (hb : (canonicalBoundaryOps (α := α)).nonExistent b) :
    (canonicalBoundaryOps (α := α)).nonExistent (a ⊓ b) := by
  unfold BoundaryOps.nonExistent at ha hb ⊢
  calc
    (canonicalBoundaryOps (α := α)).boundary (a ⊓ b)
        = ((canonicalBoundaryOps (α := α)).boundary a ⊓ b) ⊔
            (a ⊓ (canonicalBoundaryOps (α := α)).boundary b) :=
          canonical_boundary_inf (a := a) (b := b)
    _ = (⊥ : α) := by
          rw [ha, hb]
          simp

theorem canonical_impossible_inf_elim
    {α : Type _} [BiheytingAlgebra α] (a b : α)
    (h : (canonicalBoundaryOps (α := α)).impossible (a ⊓ b)) :
    (canonicalBoundaryOps (α := α)).impossible a ∨
      (canonicalBoundaryOps (α := α)).impossible b := by
  classical
  by_contra hNone
  have hNotA : ¬ (canonicalBoundaryOps (α := α)).impossible a := by
    intro hA
    exact hNone (Or.inl hA)
  have hNotB : ¬ (canonicalBoundaryOps (α := α)).impossible b := by
    intro hB
    exact hNone (Or.inr hB)
  have hAne : (canonicalBoundaryOps (α := α)).nonExistent a := by
    have hNotNonEx :
        ¬ ¬ (canonicalBoundaryOps (α := α)).nonExistent a := by
      intro hNotNe
      exact hNotA ((BoundaryOps.impossible_iff_not_nonExistent
        (canonicalBoundaryOps (α := α)) a).2 hNotNe)
    exact Classical.not_not.mp hNotNonEx
  have hBne : (canonicalBoundaryOps (α := α)).nonExistent b := by
    have hNotNonEx :
        ¬ ¬ (canonicalBoundaryOps (α := α)).nonExistent b := by
      intro hNotNe
      exact hNotB ((BoundaryOps.impossible_iff_not_nonExistent
        (canonicalBoundaryOps (α := α)) b).2 hNotNe)
    exact Classical.not_not.mp hNotNonEx
  have hInfNe :
      (canonicalBoundaryOps (α := α)).nonExistent (a ⊓ b) :=
    canonical_nonExistent_inf (a := a) (b := b) hAne hBne
  have hInfNotNe :
      ¬ (canonicalBoundaryOps (α := α)).nonExistent (a ⊓ b) :=
    (BoundaryOps.impossible_iff_not_nonExistent
      (canonicalBoundaryOps (α := α)) (a ⊓ b)).1 h
  exact hInfNotNe hInfNe

@[simp] theorem canonical_boundary_prod
    {α β : Type _} [BiheytingAlgebra α] [BiheytingAlgebra β] (a : α) (b : β) :
    (canonicalBoundaryOps (α := α × β)).boundary (a, b) =
      ((canonicalBoundaryOps (α := α)).boundary a, (canonicalBoundaryOps (α := β)).boundary b) := by
  rfl

theorem canonical_nonExistent_prod_iff
    {α β : Type _} [BiheytingAlgebra α] [BiheytingAlgebra β] (a : α) (b : β) :
    (canonicalBoundaryOps (α := α × β)).nonExistent (a, b) ↔
      (canonicalBoundaryOps (α := α)).nonExistent a ∧
        (canonicalBoundaryOps (α := β)).nonExistent b := by
  unfold BoundaryOps.nonExistent
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · intro h
    exact Prod.ext h.1 h.2

theorem canonical_impossible_prod_left
    {α β : Type _} [BiheytingAlgebra α] [BiheytingAlgebra β] (a : α) (b : β)
    (ha : (canonicalBoundaryOps (α := α)).impossible a) :
    (canonicalBoundaryOps (α := α × β)).impossible (a, b) := by
  unfold BoundaryOps.impossible at ha ⊢
  intro hPair
  exact ha (congrArg Prod.fst hPair)

theorem canonical_impossible_prod_right
    {α β : Type _} [BiheytingAlgebra α] [BiheytingAlgebra β] (a : α) (b : β)
    (hb : (canonicalBoundaryOps (α := β)).impossible b) :
    (canonicalBoundaryOps (α := α × β)).impossible (a, b) := by
  unfold BoundaryOps.impossible at hb ⊢
  intro hPair
  exact hb (congrArg Prod.snd hPair)

theorem canonical_impossible_prod_elim
    {α β : Type _} [BiheytingAlgebra α] [BiheytingAlgebra β] (a : α) (b : β)
    (h : (canonicalBoundaryOps (α := α × β)).impossible (a, b)) :
    (canonicalBoundaryOps (α := α)).impossible a ∨
      (canonicalBoundaryOps (α := β)).impossible b := by
  classical
  by_contra hNone
  push_neg at hNone
  have hNotImpA : ¬ (canonicalBoundaryOps (α := α)).impossible a := hNone.1
  have hNotImpB : ¬ (canonicalBoundaryOps (α := β)).impossible b := hNone.2
  have hA : (canonicalBoundaryOps (α := α)).nonExistent a := by
    by_contra hNotNonEx
    exact hNotImpA ((BoundaryOps.impossible_iff_not_nonExistent
      (canonicalBoundaryOps (α := α)) a).2 hNotNonEx)
  have hB : (canonicalBoundaryOps (α := β)).nonExistent b := by
    by_contra hNotNonEx
    exact hNotImpB ((BoundaryOps.impossible_iff_not_nonExistent
      (canonicalBoundaryOps (α := β)) b).2 hNotNonEx)
  have hPairNe : (canonicalBoundaryOps (α := α × β)).nonExistent (a, b) := by
    exact (canonical_nonExistent_prod_iff (a := a) (b := b)).2 ⟨hA, hB⟩
  have hPairNotNe : ¬ (canonicalBoundaryOps (α := α × β)).nonExistent (a, b) :=
    (BoundaryOps.impossible_iff_not_nonExistent
      (canonicalBoundaryOps (α := α × β)) (a, b)).1 h
  exact hPairNotNe hPairNe

/-- Set-based boundary operators for Surreal pre-games:
co-negation is complement and boundary is co-Heyting boundary. -/
noncomputable def setBoundaryOps : BoundaryOps (Set PreGame) where
  coNeg := Set.compl
  boundary := fun A => A ∩ Aᶜ
  boundary_eq_inf_coNeg := by
    intro A
    rfl

@[simp] theorem set_coNeg_eq_compl (A : Set PreGame) :
    setBoundaryOps.coNeg A = Aᶜ := rfl

@[simp] theorem set_boundary_eq_inter_compl (A : Set PreGame) :
    setBoundaryOps.boundary A = A ∩ Aᶜ := by
  rfl

@[simp] theorem set_boundary_eq_coheyting (A : Set PreGame) :
    setBoundaryOps.boundary A = Coheyting.boundary A := by
  calc
    setBoundaryOps.boundary A = (∅ : Set PreGame) := by
      change A ∩ Aᶜ = (∅ : Set PreGame)
      exact Set.inter_compl_self A
    _ = Coheyting.boundary A := by
      exact (Coheyting.boundary_eq_bot (a := A)).symm

@[simp] theorem set_boundary_eq_empty (A : Set PreGame) :
    setBoundaryOps.boundary A = (∅ : Set PreGame) := by
  change A ∩ Aᶜ = (∅ : Set PreGame)
  exact Set.inter_compl_self A

theorem set_nonExistent_all (A : Set PreGame) :
    setBoundaryOps.nonExistent A := by
  unfold BoundaryOps.nonExistent
  exact set_boundary_eq_empty A

theorem set_not_impossible (A : Set PreGame) :
    ¬ setBoundaryOps.impossible A := by
  unfold BoundaryOps.impossible
  rw [set_boundary_eq_empty]
  simp

theorem set_boundary_antitone {A B : Set PreGame} (_hAB : A ⊆ B) :
    setBoundaryOps.boundary B ⊆ setBoundaryOps.boundary A := by
  simp

/-! ### Non-Boolean witness carrier (`Fin 3`) for SN-017 next tranche -/

def fin3BoundaryOps : BoundaryOps (Fin 3) :=
  canonicalBoundaryOps (α := Fin 3)

@[simp] theorem fin3_boundary_zero :
    fin3BoundaryOps.boundary (0 : Fin 3) = 0 := by
  native_decide

@[simp] theorem fin3_boundary_one :
    fin3BoundaryOps.boundary (1 : Fin 3) = 1 := by
  native_decide

theorem fin3_nonExistent_zero :
    fin3BoundaryOps.nonExistent (0 : Fin 3) := by
  unfold BoundaryOps.nonExistent
  change fin3BoundaryOps.boundary (0 : Fin 3) = (0 : Fin 3)
  exact fin3_boundary_zero

theorem fin3_impossible_one :
    fin3BoundaryOps.impossible (1 : Fin 3) := by
  unfold BoundaryOps.impossible fin3BoundaryOps canonicalBoundaryOps Coheyting.boundary
  native_decide

theorem fin3_exists_impossible :
    ∃ a : Fin 3, fin3BoundaryOps.impossible a := by
  exact ⟨1, fin3_impossible_one⟩

theorem fin3_not_all_nonExistent :
    ¬ ∀ a : Fin 3, fin3BoundaryOps.nonExistent a := by
  intro hAll
  have hNotNonEx : ¬ fin3BoundaryOps.nonExistent (1 : Fin 3) :=
    (BoundaryOps.impossible_iff_not_nonExistent fin3BoundaryOps 1).1 fin3_impossible_one
  exact hNotNonEx (hAll 1)

theorem fin3_one_has_no_complement :
    ¬ ∃ b : Fin 3, (1 : Fin 3) ⊓ b = (0 : Fin 3) ∧ (1 : Fin 3) ⊔ b = (2 : Fin 3) := by
  native_decide

def fin3ProdBoundaryOps : BoundaryOps (Fin 3 × Fin 3) :=
  canonicalBoundaryOps (α := Fin 3 × Fin 3)

@[simp] theorem fin3Prod_boundary_zero :
    fin3ProdBoundaryOps.boundary ((0 : Fin 3), (0 : Fin 3)) = ((0 : Fin 3), (0 : Fin 3)) := by
  native_decide

@[simp] theorem fin3Prod_boundary_mid :
    fin3ProdBoundaryOps.boundary ((1 : Fin 3), (0 : Fin 3)) = ((1 : Fin 3), (0 : Fin 3)) := by
  native_decide

@[simp] theorem fin3Prod_boundary_top :
    fin3ProdBoundaryOps.boundary ((2 : Fin 3), (2 : Fin 3)) = ((0 : Fin 3), (0 : Fin 3)) := by
  native_decide

theorem fin3Prod_nonExistent_zero :
    fin3ProdBoundaryOps.nonExistent ((0 : Fin 3), (0 : Fin 3)) := by
  unfold BoundaryOps.nonExistent fin3ProdBoundaryOps canonicalBoundaryOps Coheyting.boundary
  native_decide

theorem fin3Prod_impossible_mid :
    fin3ProdBoundaryOps.impossible ((1 : Fin 3), (0 : Fin 3)) := by
  unfold BoundaryOps.impossible
  native_decide

theorem fin3Prod_exists_nonExistent :
    ∃ a : Fin 3 × Fin 3, fin3ProdBoundaryOps.nonExistent a := by
  exact ⟨((0 : Fin 3), (0 : Fin 3)), fin3Prod_nonExistent_zero⟩

theorem fin3Prod_exists_impossible :
    ∃ a : Fin 3 × Fin 3, fin3ProdBoundaryOps.impossible a := by
  exact ⟨((1 : Fin 3), (0 : Fin 3)), fin3Prod_impossible_mid⟩

theorem fin3Prod_not_all_nonExistent :
    ¬ ∀ a : Fin 3 × Fin 3, fin3ProdBoundaryOps.nonExistent a := by
  intro hAll
  have hNotNonEx : ¬ fin3ProdBoundaryOps.nonExistent ((1 : Fin 3), (0 : Fin 3)) :=
    (BoundaryOps.impossible_iff_not_nonExistent fin3ProdBoundaryOps ((1 : Fin 3), (0 : Fin 3))).1
      fin3Prod_impossible_mid
  exact hNotNonEx (hAll ((1 : Fin 3), (0 : Fin 3)))

theorem fin3Prod_mid_has_no_complement :
    ¬ ∃ b : Fin 3 × Fin 3,
      ((1 : Fin 3), (0 : Fin 3)) ⊓ b = ((0 : Fin 3), (0 : Fin 3)) ∧
      ((1 : Fin 3), (0 : Fin 3)) ⊔ b = ((2 : Fin 3), (2 : Fin 3)) := by
  rintro ⟨b, hInf, hSup⟩
  have hInfFst : (1 : Fin 3) ⊓ b.1 = (0 : Fin 3) := by
    exact congrArg Prod.fst hInf
  have hSupFst : (1 : Fin 3) ⊔ b.1 = (2 : Fin 3) := by
    exact congrArg Prod.fst hSup
  exact fin3_one_has_no_complement ⟨b.1, hInfFst, hSupFst⟩

theorem fin3Prod_impossible_inf_elim
    (a b : Fin 3 × Fin 3)
    (h : fin3ProdBoundaryOps.impossible (a ⊓ b)) :
    fin3ProdBoundaryOps.impossible a ∨ fin3ProdBoundaryOps.impossible b := by
  simpa [fin3ProdBoundaryOps] using
    (canonical_impossible_inf_elim (a := a) (b := b) h)

end Surreal
end Numbers
end HeytingLean
