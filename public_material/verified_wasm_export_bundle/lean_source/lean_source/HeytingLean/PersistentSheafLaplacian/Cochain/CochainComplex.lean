import HeytingLean.PersistentSheafLaplacian.Basic.CellularSheaf
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.LinearAlgebra.Pi

namespace HeytingLean
namespace PersistentSheafLaplacian

open SimplicialComplex

namespace Cochain

variable {V : Type*} [DecidableEq V] {K : SimplicialComplex V}

private lemma exists_insert_of_subset_card_succ {s t : Finset V} (hsub : s ⊆ t)
    (hcard : t.card = s.card + 1) :
    ∃ a, a ∉ s ∧ t = insert a s := by
  have hdiff_card : (t \ s).card = 1 := by
    rw [Finset.card_sdiff]
    rw [Finset.inter_eq_left.mpr hsub]
    omega
  rcases Finset.card_eq_one.mp hdiff_card with ⟨a0, hdiff⟩
  refine ⟨a0, ?_, ?_⟩
  · intro ha
    have : a0 ∈ t \ s := by
      rw [hdiff]
      simp
    exact (Finset.mem_sdiff.mp this).2 ha
  · ext y
    constructor
    · intro hy
      by_cases hsy : y ∈ s
      · simp [hsy]
      · have htys : y ∈ t \ s := Finset.mem_sdiff.mpr ⟨hy, hsy⟩
        have : y = a0 := by
          rw [hdiff] at htys
          simpa using htys
        simp [this]
    · intro hy
      rcases Finset.mem_insert.mp hy with hya | hsy
      · subst hya
        have : y ∈ t \ s := by
          rw [hdiff]
          simp
        exact (Finset.mem_sdiff.mp this).1
      · exact hsub hsy

private lemma exists_two_inserts_of_subset_card_two {s t : Finset V} (hsub : s ⊆ t)
    (hcard : t.card = s.card + 2) :
    ∃ a b, a ≠ b ∧ a ∉ s ∧ b ∉ s ∧ t = insert a (insert b s) := by
  have hdiff_card : (t \ s).card = 2 := by
    rw [Finset.card_sdiff]
    rw [Finset.inter_eq_left.mpr hsub]
    omega
  rcases Finset.card_eq_two.mp hdiff_card with ⟨a0, b0, hab, hdiff⟩
  refine ⟨a0, b0, hab, ?_, ?_, ?_⟩
  · intro ha
    have : a0 ∈ t \ s := by
      rw [hdiff]
      simp
    exact (Finset.mem_sdiff.mp this).2 ha
  · intro hb
    have : b0 ∈ t \ s := by
      rw [hdiff]
      simp
    exact (Finset.mem_sdiff.mp this).2 hb
  · ext x
    constructor
    · intro hx
      by_cases hsx : x ∈ s
      · simp [hsx]
      · have htxs : x ∈ t \ s := Finset.mem_sdiff.mpr ⟨hx, hsx⟩
        have hxab : x = a0 ∨ x = b0 := by
          rw [hdiff] at htxs
          simp at htxs
          exact htxs
        rcases hxab with rfl | rfl
        · simp
        · simp
    · intro hx
      rcases Finset.mem_insert.mp hx with hxa | hx
      · subst hxa
        have : x ∈ t \ s := by
          rw [hdiff]
          simp
        exact (Finset.mem_sdiff.mp this).1
      · rcases Finset.mem_insert.mp hx with hxb | hsx
        · subst hxb
          have : x ∈ t \ s := by
            rw [hdiff]
            simp
          exact (Finset.mem_sdiff.mp this).1
        · exact hsub hsx

private lemma intermediate_eq_one_of_two_inserts {s t u : Finset V}
    {a b : V} (hab : a ≠ b) (ha : a ∉ s) (hb : b ∉ s)
    (ht : t = insert a (insert b s))
    (hsu : s ⊆ u) (hut : u ⊆ t)
    (hcard : u.card = s.card + 1) :
    u = insert a s ∨ u = insert b s := by
  rcases exists_insert_of_subset_card_succ hsu hcard with ⟨c, hc, rfl⟩
  have hct : c ∈ t := hut (by simp)
  rw [ht] at hct
  have hct' : c = a ∨ c = b := by
    rcases Finset.mem_insert.mp hct with hca | hct
    · exact Or.inl hca
    · rcases Finset.mem_insert.mp hct with hcb | hcs
      · exact Or.inr hcb
      · exact False.elim (hc hcs)
  rcases hct' with rfl | rfl
  · left
    simp
  · right
    simp

private lemma simplex_between_two_step_face_eq {q : Nat}
    {σ : K.qSimplices q} {τ : K.qSimplices (q + 1)} {ρ : K.qSimplices (q + 2)}
    (hσρ : σ.1 ≤ ρ.1) (hστ : σ.1 ≤ τ.1) (hτρ : τ.1 ≤ ρ.1) :
    ∃ a b, a ≠ b ∧ a ∉ σ.1.1 ∧ b ∉ σ.1.1 ∧
      ρ.1.1 = insert a (insert b σ.1.1) ∧
      (τ.1.1 = insert a σ.1.1 ∨ τ.1.1 = insert b σ.1.1) := by
  have hρcard : ρ.1.1.card = σ.1.1.card + 2 := by
    rw [show ρ.1.1.card = q + 3 by
      simpa [SimplicialComplex.qSimplices] using
        (SimplicialComplex.mem_qSimplices (K := K) (σ := ρ.1) (q := q + 2)).mp ρ.2]
    rw [show σ.1.1.card = q + 1 by
      simpa [SimplicialComplex.qSimplices] using
        (SimplicialComplex.mem_qSimplices (K := K) (σ := σ.1) (q := q)).mp σ.2]
  rcases exists_two_inserts_of_subset_card_two hσρ hρcard with
    ⟨a, b, hab, ha, hb, hρshape⟩
  have hτcard : τ.1.1.card = σ.1.1.card + 1 := by
    rw [show τ.1.1.card = q + 2 by
      simpa [SimplicialComplex.qSimplices] using
        (SimplicialComplex.mem_qSimplices (K := K) (σ := τ.1) (q := q + 1)).mp τ.2]
    rw [show σ.1.1.card = q + 1 by
      simpa [SimplicialComplex.qSimplices] using
        (SimplicialComplex.mem_qSimplices (K := K) (σ := σ.1) (q := q)).mp σ.2]
  rcases intermediate_eq_one_of_two_inserts hab ha hb hρshape hστ hτρ hτcard with
    hτshape | hτshape
  · exact ⟨a, b, hab, ha, hb, hρshape, Or.inl hτshape⟩
  · exact ⟨a, b, hab, ha, hb, hρshape, Or.inr hτshape⟩

/-- The `q`-cochains of a cellular sheaf are sections over the `q`-simplices. -/
abbrev CochainGroup (F : CellularSheaf K) (q : Nat) : Type _ :=
  ∀ σ : K.qSimplices q, F.stalkType σ.1

/-- The contribution of a single `q`-simplex to a `(q+1)`-cochain entry. -/
noncomputable def faceTerm (F : CellularSheaf K) (o : Orientation K) (q : Nat)
    (f : CochainGroup F q) (τ : K.qSimplices (q + 1)) (σ : K.qSimplices q) :
    F.stalkType τ.1 :=
  if hface : σ.1 ≤ τ.1 then
    (((Orientation.signedIncidence o hface : ℤ) : ℝ) • F.restriction hface (f σ))
  else
    0

lemma faceTerm_add (F : CellularSheaf K) (o : Orientation K) (q : Nat)
    (f g : CochainGroup F q) (τ : K.qSimplices (q + 1)) (σ : K.qSimplices q) :
    faceTerm F o q (f + g) τ σ = faceTerm F o q f τ σ + faceTerm F o q g τ σ := by
  by_cases hface : σ.1 ≤ τ.1
  · simp [faceTerm, hface, smul_add]
  · simp [faceTerm, hface]

lemma faceTerm_smul (F : CellularSheaf K) (o : Orientation K) (q : Nat)
    (a : ℝ) (f : CochainGroup F q) (τ : K.qSimplices (q + 1)) (σ : K.qSimplices q) :
    faceTerm F o q (a • f) τ σ = a • faceTerm F o q f τ σ := by
  by_cases hface : σ.1 ≤ τ.1
  · simp [faceTerm, hface, smul_smul, mul_comm]
  · simp [faceTerm, hface]

/-- The sheaf coboundary operator induced by the signed incidence relation. -/
noncomputable def coboundary (F : CellularSheaf K) (o : Orientation K) (q : Nat) :
    CochainGroup F q →ₗ[ℝ] CochainGroup F (q + 1) where
  toFun := fun f τ => Finset.sum (K.qSimplices q).attach (fun σ => faceTerm F o q f τ σ)
  map_add' f g := by
    classical
    ext τ
    simp_rw [faceTerm_add, Pi.add_apply]
    change
      Finset.sum (K.qSimplices q).attach
          (fun σ => faceTerm F o q f τ σ + faceTerm F o q g τ σ) =
        Finset.sum (K.qSimplices q).attach (fun σ => faceTerm F o q f τ σ) +
          Finset.sum (K.qSimplices q).attach (fun σ => faceTerm F o q g τ σ)
    exact Finset.sum_add_distrib
  map_smul' a f := by
    classical
    ext τ
    simp_rw [faceTerm_smul]
    change
      Finset.sum (K.qSimplices q).attach (fun σ => a • faceTerm F o q f τ σ) =
        a • Finset.sum (K.qSimplices q).attach (fun σ => faceTerm F o q f τ σ)
    symm
    exact Finset.smul_sum

lemma coboundary_piSingle (F : CellularSheaf K) (o : Orientation K) (q : Nat)
    (σ : K.qSimplices q) (x : F.stalkType σ.1) (τ : K.qSimplices (q + 1)) :
    coboundary F o q (Pi.single σ x) τ =
      if hface : σ.1 ≤ τ.1 then
        (((Orientation.signedIncidence o hface : ℤ) : ℝ) • F.restriction hface x)
      else
        0 := by
  classical
  by_cases hface : σ.1 ≤ τ.1
  · dsimp [coboundary]
    have hsum :
        (∑ σ' ∈ (K.qSimplices q).attach, faceTerm F o q (Pi.single σ x) τ σ') =
          (((Orientation.signedIncidence o hface : ℤ) : ℝ) • F.restriction hface x) := by
      rw [Finset.sum_eq_single_of_mem σ (by simp)]
      · simp [faceTerm, hface]
      · intro σ' hσ' hne
        by_cases hface' : σ'.1 ≤ τ.1
        · simp [faceTerm, hface', hne]
        · simp [faceTerm, hface']
    simpa [hface] using hsum
  · dsimp [coboundary]
    have hsum :
        (∑ σ' ∈ (K.qSimplices q).attach, faceTerm F o q (Pi.single σ x) τ σ') =
          (0 : F.stalkType τ.1) := by
      refine Finset.sum_eq_zero ?_
      intro σ' hσ'
      by_cases hface' : σ'.1 ≤ τ.1
      · by_cases hEq : σ' = σ
        · subst hEq
          contradiction
        · simp [faceTerm, hface', hEq]
      · simp [faceTerm, hface']
    simpa [hface] using hsum

lemma delta_comp_piSingle_apply (F : CellularSheaf K) (o : Orientation K) (q : Nat)
    (σ : K.qSimplices q) (x : F.stalkType σ.1) (ρ : K.qSimplices (q + 2)) :
    (coboundary F o (q + 1) (coboundary F o q (Pi.single σ x))) ρ =
      ∑ τ' ∈ (K.qSimplices (q + 1)).attach,
        if hτρ : τ'.1 ≤ ρ.1 then
          (((Orientation.signedIncidence o hτρ : ℤ) : ℝ) •
            F.restriction hτρ
              (if hστ : σ.1 ≤ τ'.1 then
                (((Orientation.signedIncidence o hστ : ℤ) : ℝ) • F.restriction hστ x)
              else
                0))
        else
          0 := by
  classical
  dsimp [coboundary]
  refine Finset.sum_congr rfl ?_
  intro τ' hτ'
  by_cases hτρ : τ'.1 ≤ ρ.1
  · simpa [faceTerm, hτρ, coboundary] using congrArg
      (fun z => (((Orientation.signedIncidence o hτρ : ℤ) : ℝ) • F.restriction hτρ z))
      (coboundary_piSingle F o q σ x τ')
  · simp [faceTerm, hτρ]

lemma delta_comp_piSingle_apply_eq_zero_of_not_face (F : CellularSheaf K) (o : Orientation K)
    (q : Nat) (σ : K.qSimplices q) (x : F.stalkType σ.1) (ρ : K.qSimplices (q + 2))
    (hσρ : ¬ σ.1 ≤ ρ.1) :
    (coboundary F o (q + 1) (coboundary F o q (Pi.single σ x))) ρ = 0 := by
  classical
  rw [delta_comp_piSingle_apply]
  refine Finset.sum_eq_zero ?_
  intro τ' hτ'
  by_cases hτρ : τ'.1 ≤ ρ.1
  · by_cases hστ : σ.1 ≤ τ'.1
    · exact False.elim (hσρ (SimplicialComplex.face_trans (K := K) hστ hτρ))
    · simp [hτρ, hστ]
  · simp [hτρ]

theorem restriction_comp_apply (F : CellularSheaf K) {σ τ ρ : K.Simplex}
    (hστ : σ ≤ τ) (hτρ : τ ≤ ρ) (x : F.stalkType σ) :
    F.restriction hτρ (F.restriction hστ x) =
      F.restriction (SimplicialComplex.face_trans (K := K) hστ hτρ) x := by
  exact LinearMap.congr_fun (F.comp_law hστ hτρ) x

end Cochain

section DeltaSquaredSorted

open Cochain Orientation

variable {V : Type*} [DecidableEq V] [LinearOrder V] {K : SimplicialComplex V}

/-- For the sorted orientation, δ² kills Pi.single basis elements: the non-face case. -/
theorem delta_comp_piSingle_eq_zero_sorted_nonface (F : CellularSheaf K) (q : Nat)
    (σ : K.qSimplices q) (x : F.stalkType σ.1)
    (ρ : K.qSimplices (q + 2)) (hσρ : ¬ σ.1 ≤ ρ.1) :
    (Cochain.coboundary F (Orientation.sortedOrientation K) (q + 1)
      (Cochain.coboundary F (Orientation.sortedOrientation K) q (Pi.single σ x))) ρ = 0 :=
  delta_comp_piSingle_apply_eq_zero_of_not_face F _ q σ x ρ hσρ

private lemma insert_sub_self_eq_singleton {s : Finset V} {a : V} (ha : a ∉ s) :
    (insert a s) \ s = {a} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hxa | hxs, hxns⟩
    · exact hxa
    · exact absurd hxs hxns
  · rintro rfl
    exact ⟨Or.inl rfl, ha⟩

private lemma insert_ab_sub_insert_a_eq_singleton {s : Finset V} {a b : V}
    (hab : a ≠ b) (ha : a ∉ s) (hb : b ∉ s) :
    (insert a (insert b s)) \ (insert a s) = {b} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hxa | hxb | hxs, hxnas⟩
    · exact absurd (Or.inl hxa) hxnas
    · exact hxb
    · exact absurd (Or.inr hxs) hxnas
  · rintro rfl
    exact ⟨Or.inr (Or.inl rfl), by simp [Ne.symm hab, hb]⟩

private lemma insert_ab_sub_insert_b_eq_singleton {s : Finset V} {a b : V}
    (hab : a ≠ b) (ha : a ∉ s) (hb : b ∉ s) :
    (insert a (insert b s)) \ (insert b s) = {a} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hxa | hxb | hxs, hxnbs⟩
    · exact hxa
    · exact absurd (Or.inl hxb) hxnbs
    · exact absurd (Or.inr hxs) hxnbs
  · rintro rfl
    exact ⟨Or.inl rfl, by simp [hab, ha]⟩

private lemma singleton_toList (a : V) : ({a} : Finset V).toList = [a] := by
  have hmem : ∀ x, x ∈ ({a} : Finset V).toList ↔ x = a := by
    simp [Finset.mem_toList]
  have hlen : ({a} : Finset V).toList.length = 1 := by
    rw [Finset.length_toList]; exact Finset.card_singleton a
  match ({a} : Finset V).toList, hlen, hmem with
  | [x], _, hmem => simp [hmem x] at *; simp [*]

private lemma intermediate_simplex_mem {q : Nat} {σ : K.qSimplices q}
    {ρ : K.qSimplices (q + 2)} {a : V} (ha : a ∉ σ.1.1) (hins : insert a σ.1.1 ⊆ ρ.1.1) :
    insert a σ.1.1 ∈ K.simplices := by
  exact K.down_closed ρ.1.2 hins ⟨a, Finset.mem_insert_self a σ.1.1⟩

private lemma intermediate_card {q : Nat} {σ : K.qSimplices q} {a : V} (ha : a ∉ σ.1.1) :
    (insert a σ.1.1).card = (q + 1) + 1 := by
  rw [Finset.card_insert_of_notMem ha]
  have := (SimplicialComplex.mem_qSimplices (K := K)).mp σ.2
  omega

private lemma intermediate_qSimplices {q : Nat} {σ : K.qSimplices q}
    {ρ : K.qSimplices (q + 2)} {a : V} (ha : a ∉ σ.1.1) (hins : insert a σ.1.1 ⊆ ρ.1.1) :
    (⟨insert a σ.1.1, intermediate_simplex_mem ha hins⟩ : K.Simplex) ∈
      K.qSimplices (q + 1) := by
  rw [SimplicialComplex.mem_qSimplices]
  exact intermediate_card ha

/-- When exactly two elements of a finset contribute non-zero values and they cancel,
    the sum is zero. -/
private lemma sum_pair_cancel {M : Type*} [AddCommGroup M]
    {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {f : ι → M} {a b : ι} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hzero : ∀ x ∈ s, x ≠ a → x ≠ b → f x = 0)
    (hcancel : f a + f b = 0) :
    ∑ x ∈ s, f x = 0 := by
  rw [← Finset.add_sum_erase s f ha]
  have hb' : b ∈ s.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  rw [← Finset.add_sum_erase (s.erase a) f hb']
  have hrest : ∀ x ∈ (s.erase a).erase b, f x = 0 := by
    intro x hx
    have hxb : x ≠ b := (Finset.mem_erase.mp hx).1
    have hxa : x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
    have hxs : x ∈ s := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2
    exact hzero x hxs hxa hxb
  rw [Finset.sum_eq_zero hrest, add_zero, hcancel]

/-- For the sorted orientation, δ² kills Pi.single basis elements: the face case.
    When σ is a codim-2 face of ρ, the two intermediate simplices contribute
    sign products that cancel via position_exponents_cancel. -/
theorem delta_comp_piSingle_eq_zero_sorted_face (F : CellularSheaf K) (q : Nat)
    (σ : K.qSimplices q) (x : F.stalkType σ.1)
    (ρ : K.qSimplices (q + 2)) (hσρ : σ.1 ≤ ρ.1) :
    (Cochain.coboundary F (Orientation.sortedOrientation K) (q + 1)
      (Cochain.coboundary F (Orientation.sortedOrientation K) q (Pi.single σ x))) ρ = 0 := by
  classical
  rw [delta_comp_piSingle_apply]
  -- Get the two distinct vertices a, b with ρ = insert a (insert b σ)
  have hρcard : ρ.1.1.card = σ.1.1.card + 2 := by
    rw [show ρ.1.1.card = (q + 2) + 1 from
      (SimplicialComplex.mem_qSimplices (K := K)).mp ρ.2]
    rw [show σ.1.1.card = q + 1 from
      (SimplicialComplex.mem_qSimplices (K := K)).mp σ.2]
  rcases exists_two_inserts_of_subset_card_two hσρ hρcard with
    ⟨a, b, hab, ha, hb, hρshape⟩
  -- Build intermediate simplices
  have hτa_sub : insert a σ.1.1 ⊆ ρ.1.1 :=
    hρshape ▸ Finset.insert_subset_insert _ (Finset.subset_insert _ _)
  have hτb_sub : insert b σ.1.1 ⊆ ρ.1.1 :=
    hρshape ▸ Finset.subset_insert a (insert b σ.1.1)
  let τa : K.Simplex := ⟨insert a σ.1.1, intermediate_simplex_mem ha hτa_sub⟩
  let τb : K.Simplex := ⟨insert b σ.1.1, intermediate_simplex_mem hb hτb_sub⟩
  have hτa_mem : τa ∈ K.qSimplices (q + 1) := intermediate_qSimplices ha hτa_sub
  have hτb_mem : τb ∈ K.qSimplices (q + 1) := intermediate_qSimplices hb hτb_sub
  -- τa ≠ τb
  have hτab : (⟨τa, hτa_mem⟩ : {x // x ∈ K.qSimplices (q + 1)}) ≠ ⟨τb, hτb_mem⟩ := by
    intro heq
    have : τa.1 = τb.1 := congrArg (fun x => x.1.1) heq
    have ha_mem : a ∈ τa.1 := Finset.mem_insert_self a σ.1.1
    rw [this] at ha_mem
    rcases Finset.mem_insert.mp ha_mem with hab' | has
    · exact hab hab'
    · exact ha has
  -- Apply sum_pair_cancel
  refine sum_pair_cancel (Finset.mem_attach _ _) (Finset.mem_attach _ _) hτab ?_ ?_
  · -- All other summands are zero
    intro τ' _ hτa' hτb'
    by_cases hτρ : τ'.1 ≤ ρ.1
    · by_cases hστ : σ.1 ≤ τ'.1
      · -- σ ≤ τ' ≤ ρ → τ'.1.1 = insert a σ.1.1 ∨ insert b σ.1.1
        have hτ'card : τ'.1.1.card = σ.1.1.card + 1 := by
          rw [show τ'.1.1.card = (q + 1) + 1 from
            (SimplicialComplex.mem_qSimplices (K := K)).mp τ'.2]
          rw [show σ.1.1.card = q + 1 from
            (SimplicialComplex.mem_qSimplices (K := K)).mp σ.2]
        rcases intermediate_eq_one_of_two_inserts hab ha hb hρshape hστ hτρ hτ'card with
          hτ'a | hτ'b
        · -- τ'.1.1 = insert a σ.1.1 = τa.1
          exfalso; apply hτa'
          exact Subtype.ext (Subtype.ext hτ'a)
        · -- τ'.1.1 = insert b σ.1.1 = τb.1
          exfalso; apply hτb'
          exact Subtype.ext (Subtype.ext hτ'b)
      · simp [hτρ, hστ]
    · simp [hτρ]
  · -- The two contributing terms cancel
    -- Resolve the dite branches for τa
    have hτaρ : (⟨τa, hτa_mem⟩ : {x // x ∈ K.qSimplices (q + 1)}).1 ≤ ρ.1 := hτa_sub
    have hστa : σ.1 ≤ (⟨τa, hτa_mem⟩ : {x // x ∈ K.qSimplices (q + 1)}).1 :=
      Finset.subset_insert a σ.1.1
    -- Resolve the dite branches for τb
    have hτbρ : (⟨τb, hτb_mem⟩ : {x // x ∈ K.qSimplices (q + 1)}).1 ≤ ρ.1 := hτb_sub
    have hστb : σ.1 ≤ (⟨τb, hτb_mem⟩ : {x // x ∈ K.qSimplices (q + 1)}).1 :=
      Finset.subset_insert b σ.1.1
    simp only [hτaρ, hστa, hτbρ, hστb, dite_true, LinearMap.map_smul]
    -- Collapse restriction compositions using the sheaf composition law
    rw [restriction_comp_apply F hστa hτaρ x, restriction_comp_apply F hστb hτbρ x]
    -- Factor: (c₁ • v) + (c₂ • v) = (c₁ + c₂) • v
    rw [smul_smul, smul_smul, ← add_smul]
    -- Suffices to show the integer coefficient is zero
    -- Set differences
    have hdiff_τa_σ : (τa.1 \ σ.1.1).toList = [a] := by
      rw [show τa.1 \ σ.1.1 = {a} from insert_sub_self_eq_singleton ha]; exact singleton_toList a
    have hdiff_ρ_τa : (ρ.1.1 \ τa.1).toList = [b] := by
      have : ρ.1.1 \ τa.1 = {b} := by rw [hρshape]; exact insert_ab_sub_insert_a_eq_singleton hab ha hb
      rw [this]; exact singleton_toList b
    have hdiff_τb_σ : (τb.1 \ σ.1.1).toList = [b] := by
      rw [show τb.1 \ σ.1.1 = {b} from insert_sub_self_eq_singleton hb]; exact singleton_toList b
    have hdiff_ρ_τb : (ρ.1.1 \ τb.1).toList = [a] := by
      have : ρ.1.1 \ τb.1 = {a} := by rw [hρshape]; exact insert_ab_sub_insert_b_eq_singleton hab ha hb
      rw [this]; exact singleton_toList a
    -- Simplify signedIncidence using sortedOrientation
    rw [Orientation.sortedOrientation_signedIncidence_mul_one hτaρ hdiff_ρ_τa,
        Orientation.sortedOrientation_signedIncidence_mul_one hστa hdiff_τa_σ,
        Orientation.sortedOrientation_signedIncidence_mul_one hτbρ hdiff_ρ_τb,
        Orientation.sortedOrientation_signedIncidence_mul_one hστb hdiff_τb_σ]
    -- Set differences for signedIncidence
    have hdiff_τa_σ : (τa.1 \ σ.1.1).toList = [a] := by
      rw [show τa.1 \ σ.1.1 = {a} from insert_sub_self_eq_singleton ha]; exact singleton_toList a
    have hdiff_ρ_τa : (ρ.1.1 \ τa.1).toList = [b] := by
      have : ρ.1.1 \ τa.1 = {b} := by rw [hρshape]; exact insert_ab_sub_insert_a_eq_singleton hab ha hb
      rw [this]; exact singleton_toList b
    have hdiff_τb_σ : (τb.1 \ σ.1.1).toList = [b] := by
      rw [show τb.1 \ σ.1.1 = {b} from insert_sub_self_eq_singleton hb]; exact singleton_toList b
    have hdiff_ρ_τb : (ρ.1.1 \ τb.1).toList = [a] := by
      have : ρ.1.1 \ τb.1 = {a} := by rw [hρshape]; exact insert_ab_sub_insert_b_eq_singleton hab ha hb
      rw [this]; exact singleton_toList a
    -- Memberships in ρ
    have ha_ρ : a ∈ ρ.1.1 := hτa_sub (Finset.mem_insert_self a σ.1.1)
    have hb_ρ : b ∈ ρ.1.1 := hτb_sub (Finset.mem_insert_self b σ.1.1)
    -- τa = ρ.erase b, τb = ρ.erase a (as Finsets)
    have hτa_eq : τa.1 = ρ.1.1.erase b := by
      show insert a σ.1.1 = ρ.1.1.erase b
      rw [hρshape]
      ext x
      simp only [Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (rfl | hxs)
        · exact ⟨hab, Or.inl rfl⟩
        · exact ⟨fun hxb => hb (hxb ▸ hxs), Or.inr (Or.inr hxs)⟩
      · rintro ⟨hxb, rfl | rfl | hxs⟩
        · exact Or.inl rfl
        · exact absurd rfl hxb
        · exact Or.inr hxs
    have hτb_eq : τb.1 = ρ.1.1.erase a := by
      show insert b σ.1.1 = ρ.1.1.erase a
      rw [hρshape]
      ext x
      simp only [Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (rfl | hxs)
        · exact ⟨Ne.symm hab, Or.inr (Or.inl rfl)⟩
        · exact ⟨fun hxa => ha (hxa ▸ hxs), Or.inr (Or.inr hxs)⟩
      · rintro ⟨hxa, rfl | rfl | hxs⟩
        · exact absurd rfl hxa
        · exact Or.inl rfl
        · exact Or.inr hxs
    -- sort(τa) = ρ.sort.erase b, sort(τb) = ρ.sort.erase a
    have hτa_sort : τa.1.sort (· ≤ ·) = (ρ.1.1.sort (· ≤ ·)).erase b := by
      rw [hτa_eq]; exact Orientation.sort_erase_eq_erase_sort hb_ρ
    have hτb_sort : τb.1.sort (· ≤ ·) = (ρ.1.1.sort (· ≤ ·)).erase a := by
      rw [hτb_eq]; exact Orientation.sort_erase_eq_erase_sort ha_ρ
    -- Simplify: simp resolves dite, pushes smul through restriction,
    -- collapses compositions (proof irrelevance), combines smul, and
    -- converts signedIncidence to alternatingSign for the sorted orientation.
    simp only [hτaρ, hστa, hτbρ, hστb, dite_true, LinearMap.map_smul]
    -- Goal is now: (ℝ-coefficient) • F.restriction(hσρ) x = 0
    -- Rewrite τa.sort and τb.sort
    rw [hτa_sort, hτb_sort]
    -- Collapse ℝ products to ℤ products, apply alternatingSign_mul
    simp only [← Int.cast_mul, alternatingSign_mul, ← Int.cast_add]
    -- Now the coefficient is ↑(position_exponents expression)
    have ha_sort : a ∈ ρ.1.1.sort (· ≤ ·) := by
      rw [Finset.mem_sort (· ≤ ·)]; exact ha_ρ
    have hb_sort : b ∈ ρ.1.1.sort (· ≤ ·) := by
      rw [Finset.mem_sort (· ≤ ·)]; exact hb_ρ
    have hcancel := position_exponents_cancel
      (Finset.sort_nodup (· ≤ ·) ρ.1.1) hab ha_sort hb_sort
    simp only [hcancel, Int.cast_zero, zero_smul]

/-- For the sorted orientation, δ² kills every Pi.single basis element. -/
theorem delta_comp_piSingle_eq_zero_sorted (F : CellularSheaf K) (q : Nat)
    (σ : K.qSimplices q) (x : F.stalkType σ.1)
    (ρ : K.qSimplices (q + 2)) :
    (Cochain.coboundary F (Orientation.sortedOrientation K) (q + 1)
      (Cochain.coboundary F (Orientation.sortedOrientation K) q (Pi.single σ x))) ρ = 0 := by
  by_cases hσρ : σ.1 ≤ ρ.1
  · exact delta_comp_piSingle_eq_zero_sorted_face F q σ x ρ hσρ
  · exact delta_comp_piSingle_eq_zero_sorted_nonface F q σ x ρ hσρ

/-- A finite cochain is the sum of its `Pi.single` basis contributions. -/
theorem cochain_eq_sum_piSingle (F : CellularSheaf K) (q : Nat)
    (f : Cochain.CochainGroup F q) :
    Finset.sum (K.qSimplices q).attach
        (fun σ => (Pi.single σ (f σ) : Cochain.CochainGroup F q)) = f := by
  classical
  ext τ
  simp

/-- For the sorted orientation, the coboundary squares to zero as a linear map. -/
theorem coboundary_comp_eq_zero_sorted (F : CellularSheaf K) (q : Nat) :
    Cochain.coboundary F (Orientation.sortedOrientation K) (q + 1) ∘ₗ
      Cochain.coboundary F (Orientation.sortedOrientation K) q = 0 := by
  classical
  apply LinearMap.ext
  intro g
  have hq :
      Cochain.coboundary F (Orientation.sortedOrientation K) q g =
        Finset.sum (K.qSimplices q).attach
          (fun σ => Cochain.coboundary F (Orientation.sortedOrientation K) q (Pi.single σ (g σ))) := by
    calc
      Cochain.coboundary F (Orientation.sortedOrientation K) q g
          = Cochain.coboundary F (Orientation.sortedOrientation K) q
              (Finset.sum (K.qSimplices q).attach
                (fun σ => (Pi.single σ (g σ) : Cochain.CochainGroup F q))) := by
              rw [cochain_eq_sum_piSingle F q g]
      _ = Finset.sum (K.qSimplices q).attach
            (fun σ => Cochain.coboundary F (Orientation.sortedOrientation K) q (Pi.single σ (g σ))) := by
              rw [map_sum]
  have hqq :
      Cochain.coboundary F (Orientation.sortedOrientation K) (q + 1)
          (Cochain.coboundary F (Orientation.sortedOrientation K) q g) =
        Finset.sum (K.qSimplices q).attach
          (fun σ =>
            Cochain.coboundary F (Orientation.sortedOrientation K) (q + 1)
              (Cochain.coboundary F (Orientation.sortedOrientation K) q (Pi.single σ (g σ)))) := by
    calc
      Cochain.coboundary F (Orientation.sortedOrientation K) (q + 1)
          (Cochain.coboundary F (Orientation.sortedOrientation K) q g)
          = Cochain.coboundary F (Orientation.sortedOrientation K) (q + 1)
              (Finset.sum (K.qSimplices q).attach
                (fun σ => Cochain.coboundary F (Orientation.sortedOrientation K) q (Pi.single σ (g σ)))) := by
                  rw [hq]
      _ = Finset.sum (K.qSimplices q).attach
            (fun σ =>
              Cochain.coboundary F (Orientation.sortedOrientation K) (q + 1)
                (Cochain.coboundary F (Orientation.sortedOrientation K) q (Pi.single σ (g σ)))) := by
                  rw [map_sum]
  ext ρ
  change (Cochain.coboundary F (Orientation.sortedOrientation K) (q + 1)
      ((Cochain.coboundary F (Orientation.sortedOrientation K) q) g)) ρ = 0
  rw [hqq]
  have hsumzero :
      Finset.sum (K.qSimplices q).attach
        (fun σ =>
          (Cochain.coboundary F (Orientation.sortedOrientation K) (q + 1)
            (Cochain.coboundary F (Orientation.sortedOrientation K) q (Pi.single σ (g σ)))) ρ) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro σ _
    exact delta_comp_piSingle_eq_zero_sorted F q σ (g σ) ρ
  simpa using hsumzero

end DeltaSquaredSorted

end PersistentSheafLaplacian
end HeytingLean
