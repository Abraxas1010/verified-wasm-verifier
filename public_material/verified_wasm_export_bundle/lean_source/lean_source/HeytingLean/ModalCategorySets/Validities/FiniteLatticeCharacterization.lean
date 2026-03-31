import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import HeytingLean.ModalCategorySets.Validities.BooleanFrames
import HeytingLean.ModalCategorySets.Validities.GrzFinite
import HeytingLean.ModalCategorySets.Validities.PointedLabeling

namespace HeytingLean.ModalCategorySets.Validities

open HeytingLean.ModalCategorySets.Propositional
open scoped Classical

universe u v w

namespace FiniteLatticeCharacterization

noncomputable section

def canonicalVal {n : Nat} : Finset (Fin n) → Fin n → Prop :=
  fun s i => i ∈ s

def subsetPattern {n : Nat} (s : Finset (Fin n)) : Formula (Fin n) :=
  Formula.conjList <|
    (List.finRange n).map fun i =>
      if i ∈ s then .var i else Formula.neg (.var i)

def HoldsSubsetPattern {n : Nat} (s t : Finset (Fin n)) : Prop :=
  let M : Model (Finset (Fin n)) (Fin n) := mkModel (BooleanFrames.frame n) canonicalVal
  M, t ⊩ (subsetPattern s)

theorem satisfies_subsetPattern_iff {n : Nat} (s t : Finset (Fin n)) :
    HoldsSubsetPattern s t ↔ t = s := by
  rw [HoldsSubsetPattern]
  change
    ((mkModel (BooleanFrames.frame n) canonicalVal), t ⊩ Formula.conjList
      ((List.finRange n).map fun i => if i ∈ s then .var i else Formula.neg (.var i))) ↔
      t = s
  rw [satisfies_conjList_iff]
  constructor
  · intro hSat
    apply Finset.ext
    intro i
    by_cases hi : i ∈ s
    · have hMem :
          (mkModel (BooleanFrames.frame n) canonicalVal), t ⊩ .var i := by
        apply hSat
        exact List.mem_map.mpr (Exists.intro i (And.intro (by simp) (by simp [hi])))
      have ht : i ∈ t := by
        simpa [canonicalVal] using hMem
      constructor
      · intro _
        exact hi
      · intro _
        exact ht
    · have hMem :
          (mkModel (BooleanFrames.frame n) canonicalVal), t ⊩ Formula.neg (.var i) := by
        apply hSat
        exact List.mem_map.mpr (Exists.intro i (And.intro (by simp) (by simp [hi])))
      have hNot : i ∉ t := by
        intro ht
        apply hMem
        simpa [canonicalVal] using ht
      constructor
      · intro ht
        exact False.elim (hNot ht)
      · intro hs
        exact False.elim (hi hs)
  · intro hEq
    refine fun φ hφ => ?_
    rcases List.mem_map.mp hφ with ⟨i, -, rfl⟩
    by_cases hi : i ∈ s
    · subst hEq
      rw [if_pos hi]
      change i ∈ t
      exact hi
    · subst hEq
      rw [if_neg hi]
      show (mkModel (BooleanFrames.frame n) canonicalVal), t ⊩ Formula.neg (.var i)
      intro hs
      exact hi hs

def decodeSup {W : Type u} [Fintype W] [DecidableEq W] [SemilatticeSup W] [OrderBot W]
    (e : W ≃ Fin (Fintype.card W)) (s : Finset (Fin (Fintype.card W))) : W :=
  (s.image e.symm.toEmbedding).sup id

theorem decodeSup_mono {W : Type u} [Fintype W] [DecidableEq W] [SemilatticeSup W] [OrderBot W]
    (e : W ≃ Fin (Fintype.card W))
    {s t : Finset (Fin (Fintype.card W))} (hst : s ⊆ t) :
    decodeSup e s ≤ decodeSup e t := by
  unfold decodeSup
  refine Finset.sup_le ?_
  intro w hw
  rcases Finset.mem_image.mp hw with ⟨i, hi, rfl⟩
  exact Finset.le_sup (by simpa using hst hi)

theorem decodeSup_insert_eq {W : Type u} [Fintype W] [DecidableEq W] [SemilatticeSup W] [OrderBot W]
    (e : W ≃ Fin (Fintype.card W)) (s : Finset (Fin (Fintype.card W))) (w : W)
    (hLe : decodeSup e s ≤ w) :
    decodeSup e (insert (e w) s) = w := by
  apply le_antisymm
  · unfold decodeSup
    refine Finset.sup_le ?_
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨i, hi, rfl⟩
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · simp
    · exact (Finset.le_sup (by simpa using hi')).trans hLe
  · unfold decodeSup
    exact Finset.le_sup (s := (insert (e w) s).image e.symm.toEmbedding) (f := id) (by
      show w ∈ (insert (e w) s).image e.symm.toEmbedding
      simp)

def exactLabel {W : Type u} [Fintype W] [DecidableEq W] [SemilatticeSup W] [OrderBot W]
    (e : W ≃ Fin (Fintype.card W)) (w : W) : Formula (Fin (Fintype.card W)) :=
  Formula.disjList <|
    (((Finset.univ : Finset (Finset (Fin (Fintype.card W)))).filter
      fun s => decodeSup e s = w).toList.map subsetPattern)

def HoldsExactLabel {W : Type u} [Fintype W] [DecidableEq W] [SemilatticeSup W] [OrderBot W]
    (e : W ≃ Fin (Fintype.card W)) (t : Finset (Fin (Fintype.card W))) (w : W) : Prop :=
  let M : Model (Finset (Fin (Fintype.card W))) (Fin (Fintype.card W)) :=
    mkModel (BooleanFrames.frame (Fintype.card W)) canonicalVal
  M, t ⊩ (exactLabel e w)

theorem satisfies_exactLabel_iff {W : Type u}
    [Fintype W] [DecidableEq W] [SemilatticeSup W] [OrderBot W]
    (e : W ≃ Fin (Fintype.card W))
    (t : Finset (Fin (Fintype.card W))) (w : W) :
    HoldsExactLabel e t w ↔ decodeSup e t = w := by
  rw [HoldsExactLabel]
  change
    ((mkModel (BooleanFrames.frame (Fintype.card W)) canonicalVal), t ⊩ Formula.disjList
      (((Finset.univ : Finset (Finset (Fin (Fintype.card W)))).filter
        fun s => decodeSup e s = w).toList.map subsetPattern)) ↔
      decodeSup e t = w
  rw [satisfies_disjList_iff]
  constructor
  · rintro ⟨φ, hφ, hSat⟩
    rcases List.mem_map.mp hφ with ⟨s, hs, rfl⟩
    have hs' :
        s ∈ ((Finset.univ : Finset (Finset (Fin (Fintype.card W)))).filter
          fun u => decodeSup e u = w) := by
      simpa using hs
    have hDecode : decodeSup e s = w :=
      (Finset.mem_filter.mp hs').2
    have htEq : t = s :=
      (satisfies_subsetPattern_iff s t).1 hSat
    simpa [htEq] using hDecode
  · intro hDecode
    refine Exists.intro (subsetPattern t) ?_
    refine And.intro ?_ ((satisfies_subsetPattern_iff t t).2 rfl)
    apply List.mem_map.mpr
    refine Exists.intro t ?_
    refine And.intro ?_ rfl
    simp [hDecode]

/-- Semantic benchmark: truth at the bottom world of every finite join-semilattice. -/
def ValidAtBottomAllFiniteJoinSemilattices {α : Type v} (φ : Formula α) : Prop :=
  ∀ {W : Type} [Fintype W] [DecidableEq W] [SemilatticeSup W] [OrderBot W]
    (val : W → α → Prop),
      let M : Model W α := mkModel (OrderedFrames.orderFrame W) val
      (M, ⊥ ⊩ φ)

theorem validAtBottom_of_validOnAllFiniteBooleanFrames
    {α : Type v} {φ : Formula α}
    (hValid : BooleanFrames.ValidOnAllFiniteBooleanFrames φ) :
    ValidAtBottomAllFiniteJoinSemilattices φ := by
  intro W _ _ _ _ val
  let e : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
  let M : Model (Finset (Fin (Fintype.card W))) (Fin (Fintype.card W)) :=
    mkModel (BooleanFrames.frame (Fintype.card W)) canonicalVal
  have hSubstValid :
      (BooleanFrames.frame (Fintype.card W)).Valid
        (Formula.subst (labelSubst
          (labels := exactLabel e) val) φ) :=
    (hValid (Fintype.card W)).subst (labelSubst (labels := exactLabel e) val)
  have hBottom :
      (M, ∅ ⊩ Formula.subst (labelSubst
          (labels := exactLabel e) val) φ) :=
    hSubstValid canonicalVal ∅
  have hTransport :=
    satisfies_subst_iff_of_pointedLabeling
      (M := M)
      (F := OrderedFrames.orderFrame W)
      (decode := decodeSup e)
      (labels := exactLabel e)
      (val := val)
      (hExact := fun s w => by simpa [HoldsExactLabel] using satisfies_exactLabel_iff e s w)
      (hForward := fun s t hst => decodeSup_mono e hst)
      (hBack := fun s w hsw =>
        Exists.intro (insert (e w) s)
          (And.intro
            (by
              intro i hi
              exact Finset.mem_insert_of_mem hi)
            (decodeSup_insert_eq e s w hsw)))
      (x := ∅)
      (φ := φ)
  have hDecodeEmpty : decodeSup e ∅ = (⊥ : W) := by
    simp [decodeSup]
  simpa [hDecodeEmpty] using hTransport.mp hBottom

theorem validOnAllFiniteBooleanFrames_of_validAtBottom
    {α : Type v} {φ : Formula α}
    (hValid : ValidAtBottomAllFiniteJoinSemilattices φ) :
    BooleanFrames.ValidOnAllFiniteBooleanFrames φ := by
  intro n
  refine (BooleanFrames.valid_iff_validAtBottom (n := n) (φ := φ)).2 ?_
  intro val
  let M : Model (Finset (Fin n)) α := mkModel (OrderedFrames.orderFrame (Finset (Fin n))) val
  have hBottom : M, (⊥ : Finset (Fin n)) ⊩ φ := by
    simpa [M] using (@hValid (Finset (Fin n)) inferInstance inferInstance inferInstance inferInstance val)
  change (mkModel (OrderedFrames.orderFrame (Finset (Fin n))) val), (⊥ : Finset (Fin n)) ⊩ φ
  exact hBottom

theorem validOnAllFiniteBooleanFrames_iff_validAtBottom
    {α : Type v} {φ : Formula α} :
    BooleanFrames.ValidOnAllFiniteBooleanFrames φ ↔
      ValidAtBottomAllFiniteJoinSemilattices φ := by
  constructor
  · exact validAtBottom_of_validOnAllFiniteBooleanFrames
  · exact validOnAllFiniteBooleanFrames_of_validAtBottom

end

end FiniteLatticeCharacterization

end HeytingLean.ModalCategorySets.Validities
