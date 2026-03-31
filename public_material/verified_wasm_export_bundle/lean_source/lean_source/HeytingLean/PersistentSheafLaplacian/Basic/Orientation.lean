import HeytingLean.PersistentSheafLaplacian.Basic.SimplicialComplex
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Fin.SuccPred
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign

namespace HeytingLean
namespace PersistentSheafLaplacian

open SimplicialComplex

namespace Orientation

def alternatingSign (n : Nat) : ℤ :=
  if n % 2 = 0 then 1 else -1

end Orientation

/-- An orientation chooses an ordered list of the vertices of each simplex. -/
structure Orientation {V : Type*} [DecidableEq V] (K : SimplicialComplex V) where
  orderedVertices : (σ : K.Simplex) → List V
  nodup : ∀ σ, (orderedVertices σ).Nodup
  toFinset_eq : ∀ σ, (orderedVertices σ).toFinset = σ.1

namespace Orientation

variable {V : Type*} [DecidableEq V] {K : SimplicialComplex V}

/-- The face order induced on `σ` by the ordered vertices of the coface `τ`. -/
def inducedFaceVertices (o : Orientation K) {σ τ : K.Simplex} (_hστ : σ ≤ τ) : List V :=
  (o.orderedVertices τ).filter fun v => v ∈ σ.1

theorem inducedFaceVertices_trans (o : Orientation K) {σ τ ρ : K.Simplex}
    (hστ : σ ≤ τ) (hτρ : τ ≤ ρ) :
    (inducedFaceVertices o hτρ).filter (fun v => v ∈ σ.1) =
      inducedFaceVertices o (SimplicialComplex.face_trans (K := K) hστ hτρ) := by
  rw [inducedFaceVertices, inducedFaceVertices, List.filter_filter]
  apply List.filter_congr
  intro v hv
  by_cases hvs : v ∈ σ.1
  · have hvt : v ∈ τ.1 := hστ hvs
    simp [hvs, hvt]
  · simp [hvs]

private theorem inducedFaceVertices_nodup (o : Orientation K) {σ τ : K.Simplex} (hστ : σ ≤ τ) :
    (inducedFaceVertices o hστ).Nodup := by
  simpa [inducedFaceVertices] using (o.nodup τ).filter (fun v => v ∈ σ.1)

private theorem inducedFaceVertices_toFinset (o : Orientation K) {σ τ : K.Simplex} (hστ : σ ≤ τ) :
    (inducedFaceVertices o hστ).toFinset = σ.1 := by
  ext v
  simp [inducedFaceVertices, o.toFinset_eq τ]
  intro hv
  exact hστ hv

theorem inducedFaceVertices_eq_erase_of_codim1 (o : Orientation K) {σ τ : K.Simplex}
    (hστ : σ ≤ τ) {v : V} (_hvτ : v ∈ τ.1) (hvσ : v ∉ σ.1)
    (hrest : ∀ w, w ∈ τ.1 → w ≠ v → w ∈ σ.1) :
    inducedFaceVertices o hστ = (o.orderedVertices τ).erase v := by
  have hnodup := o.nodup τ
  rw [inducedFaceVertices]
  rw [hnodup.erase_eq_filter]
  apply List.filter_congr
  intro w hw
  by_cases hwv : w = v
  · simp [hwv, hvσ]
  · have hwτ : w ∈ τ.1 := by
      rw [← o.toFinset_eq τ]
      exact List.mem_toFinset.mpr hw
    have hws : w ∈ σ.1 := hrest w hwτ hwv
    simp [hwv, hws]

theorem idxOf_erase_of_lt {l : List V} (hl : l.Nodup) {a b : V} (hab : a ≠ b)
    (ha : a ∈ l) (hb : b ∈ l) (hidx : l.idxOf a < l.idxOf b) :
    (l.erase b).idxOf a = l.idxOf a := by
  induction l with
  | nil =>
      cases ha
  | cons c l ih =>
      rw [List.nodup_cons] at hl
      rcases hl with ⟨hc, hl⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rcases List.mem_cons.mp hb with hbc | hb
        · exact False.elim (hab hbc.symm)
        · simp [List.idxOf_cons_self, hab]
      · rcases List.mem_cons.mp hb with rfl | hb
        · simp [List.idxOf_cons_ne _ (Ne.symm hab)] at hidx
        · have hc_a : c ≠ a := by
            intro hca
            exact hc (hca ▸ ha)
          have hc_b : c ≠ b := by
            intro hcb
            exact hc (hcb ▸ hb)
          have htail : l.idxOf a < l.idxOf b := by
            simpa [List.idxOf_cons_ne _ hc_a, List.idxOf_cons_ne _ hc_b] using hidx
          simpa [List.idxOf_cons_ne _ hc_a, hc_b] using ih hl ha hb htail

theorem idxOf_erase_of_gt {l : List V} (hl : l.Nodup) {a b : V} (hab : a ≠ b)
    (ha : a ∈ l) (hb : b ∈ l) (hidx : l.idxOf b < l.idxOf a) :
    (l.erase b).idxOf a = l.idxOf a - 1 := by
  induction l with
  | nil =>
      cases ha
  | cons c l ih =>
      rw [List.nodup_cons] at hl
      rcases hl with ⟨hc, hl⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · rcases List.mem_cons.mp ha with hca | ha
        · exact False.elim (hab hca)
        · have hc_a : b ≠ a := by
            intro hca
            exact hc (hca ▸ ha)
          simp [List.idxOf_cons_ne _ hc_a]
      · rcases List.mem_cons.mp ha with rfl | ha
        · simp [List.idxOf_cons_self, hab] at hidx
        · have hc_a : c ≠ a := by
            intro hca
            exact hc (hca ▸ ha)
          have hc_b : c ≠ b := by
            intro hcb
            exact hc (hcb ▸ hb)
          have htail : l.idxOf b < l.idxOf a := by
            simpa [List.idxOf_cons_ne _ hc_a, List.idxOf_cons_ne _ hc_b] using hidx
          have hrec : (l.erase b).idxOf a = l.idxOf a - 1 := ih hl ha hb htail
          have hrec' : (l.erase b).idxOf a + 1 = l.idxOf a := by
            omega
          simpa [List.idxOf_cons_ne _ hc_a, hc_b] using hrec'

theorem alternatingSign_succ (n : Nat) :
    Orientation.alternatingSign (n + 1) = -Orientation.alternatingSign n := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have hs : (n + 1) % 2 = 1 := by omega
    simp [Orientation.alternatingSign, h, hs]
  · have hs : (n + 1) % 2 = 0 := by omega
    simp [Orientation.alternatingSign, h, hs]

theorem alternatingSign_add_succ_eq_zero (n : Nat) :
    Orientation.alternatingSign n + Orientation.alternatingSign (n + 1) = 0 := by
  rw [alternatingSign_succ]
  omega

theorem alternatingSign_succ_add_eq_zero (n : Nat) :
    Orientation.alternatingSign (n + 1) + Orientation.alternatingSign n = 0 := by
  rw [add_comm, alternatingSign_add_succ_eq_zero]

theorem alternatingSign_eq_neg_one_pow (n : Nat) :
    Orientation.alternatingSign n = (-1 : ℤ) ^ n := by
  induction n with
  | zero =>
      simp [Orientation.alternatingSign]
  | succ n ih =>
      rw [alternatingSign_succ, ih, pow_succ]
      simp [mul_comm]

/-- `alternatingSign` squares to `1`. -/
theorem alternatingSign_mul_self (n : Nat) :
    Orientation.alternatingSign n * Orientation.alternatingSign n = 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;>
    simp [Orientation.alternatingSign, h]

/-- alternatingSign is multiplicative: altSign(m) * altSign(n) = altSign(m + n). -/
theorem alternatingSign_mul (m n : Nat) :
    Orientation.alternatingSign m * Orientation.alternatingSign n =
      Orientation.alternatingSign (m + n) := by
  simp only [Orientation.alternatingSign]
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
    simp [hm, hn] <;> omega

theorem position_exponents_cancel {l : List V} (hl : l.Nodup) {a b : V} (hab : a ≠ b)
    (ha : a ∈ l) (hb : b ∈ l) :
    Orientation.alternatingSign (l.idxOf b + (l.erase b).idxOf a) +
      Orientation.alternatingSign (l.idxOf a + (l.erase a).idxOf b) = 0 := by
  have hne : l.idxOf a ≠ l.idxOf b := by
    intro hEq
    exact hab ((List.idxOf_inj ha hb).mp hEq)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h₁ : (l.erase b).idxOf a = l.idxOf a := idxOf_erase_of_lt hl hab ha hb hlt
    have h₂ : (l.erase a).idxOf b = l.idxOf b - 1 := by
      exact idxOf_erase_of_gt hl (Ne.symm hab) hb ha hlt
    have hk : 1 + (l.idxOf b - 1) = l.idxOf b := by omega
    rw [h₁, h₂]
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, hk] using
      (alternatingSign_succ_add_eq_zero (l.idxOf a + (l.idxOf b - 1)))
  · have h₁ : (l.erase b).idxOf a = l.idxOf a - 1 := idxOf_erase_of_gt hl hab ha hb hgt
    have h₂ : (l.erase a).idxOf b = l.idxOf b := by
      exact idxOf_erase_of_lt hl (Ne.symm hab) hb ha hgt
    have hk : 1 + (l.idxOf a - 1) = l.idxOf a := by omega
    rw [h₁, h₂]
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, hk] using
      (alternatingSign_add_succ_eq_zero (l.idxOf b + (l.idxOf a - 1)))

theorem getElem_eraseIdx_fin {l : List V} {n : Nat} (hlen : l.length = n + 1)
    (j : Fin (n + 1)) (k : Fin n) :
    (l.eraseIdx j)[k]'(by
      have hlen' : (l.eraseIdx ↑j).length = n := by
        rw [List.length_eraseIdx_of_lt]
        · omega
        · simpa [hlen] using j.is_lt
      simpa [hlen'] using k.is_lt) =
      l[j.succAbove k]'(by simpa [hlen] using (j.succAbove k).is_lt) := by
  have hk : (k : Nat) < (l.eraseIdx ↑j).length := by
    have hlen' : (l.eraseIdx ↑j).length = n := by
      rw [List.length_eraseIdx_of_lt]
      · omega
      · simpa [hlen] using j.is_lt
    simpa [hlen'] using k.is_lt
  by_cases hkj : k.castSucc < j
  · rw [Fin.succAbove_of_castSucc_lt _ _ hkj]
    simpa using
      (List.getElem_eraseIdx_of_lt (l := l) (i := ↑j) (j := ↑k) hk (by simpa using hkj))
  · have hjk : j ≤ k.castSucc := le_of_not_gt hkj
    rw [Fin.succAbove_of_le_castSucc _ _ hjk]
    simpa using
      (List.getElem_eraseIdx_of_ge (l := l) (i := ↑j) (j := ↑k) hk (by simpa using hjk))

theorem toFinset_tail_eq_erase {a : V} {l₁ l₂ : List V}
    (h₁ : (a :: l₁).Nodup) (h₂ : l₂.Nodup)
    (h : (a :: l₁).toFinset = l₂.toFinset) :
    l₁.toFinset = (l₂.erase a).toFinset := by
  ext x
  have ha_not_mem : a ∉ l₁ := (List.nodup_cons.mp h₁).1
  constructor
  · intro hx
    have hx' : x ∈ l₂.toFinset := by simpa [h] using (by simp [hx] : x ∈ (a :: l₁).toFinset)
    have hxList₁ : x ∈ l₁ := by simpa using hx
    have hxa : x ≠ a := by
      intro hxa
      exact ha_not_mem (hxa ▸ hxList₁)
    have hxList : x ∈ l₂ := by simpa using hx'
    simpa using (List.Nodup.mem_erase_iff h₂).2 ⟨hxa, hxList⟩
  · intro hx
    have hxList : x ∈ l₂.erase a := by simpa using hx
    have hx' : x ∈ l₂ := List.mem_of_mem_erase hxList
    have hxa : x ≠ a := by
      exact (List.Nodup.mem_erase_iff h₂).1 hxList |>.1
    have hxcons : x ∈ (a :: l₁).toFinset := by simpa [h] using hx'
    simpa [hxa] using hxcons

private theorem length_eq_of_toFinset_eq {l₁ l₂ : List V}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h : l₁.toFinset = l₂.toFinset) :
    l₁.length = l₂.length := by
  calc
    l₁.length = l₁.toFinset.card := by
      symm
      exact List.toFinset_card_of_nodup h₁
    _ = l₂.toFinset.card := by
      simp [h]
    _ = l₂.length := by
      exact List.toFinset_card_of_nodup h₂

private def listMembershipEquiv {l₁ l₂ : List V} (h : l₁.toFinset = l₂.toFinset) :
    {x // x ∈ l₁} ≃ {x // x ∈ l₂} where
  toFun x := ⟨x.1, by
    have hx : x.1 ∈ l₁.toFinset := by simpa using x.2
    simp [h] at hx
    exact hx⟩
  invFun x := ⟨x.1, by
    have hx : x.1 ∈ l₂.toFinset := by simpa using x.2
    have : x.1 ∈ l₁.toFinset := by
      rw [h]
      exact hx
    simpa using this⟩
  left_inv x := by
    cases x
    rfl
  right_inv x := by
    cases x
    rfl

noncomputable def reorderPerm {l₁ l₂ : List V}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h : l₁.toFinset = l₂.toFinset) :
    Equiv.Perm (Fin l₁.length) :=
  let hLen := length_eq_of_toFinset_eq h₁ h₂ h
  (((h₁.getEquiv l₁).trans (listMembershipEquiv h)).trans (h₂.getEquiv l₂).symm).trans
    (finCongr hLen.symm)

theorem get_reorderPerm {l₁ l₂ : List V}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h : l₁.toFinset = l₂.toFinset)
    (i : Fin l₁.length) :
    l₂.get ((finCongr (length_eq_of_toFinset_eq h₁ h₂ h)) (reorderPerm h₁ h₂ h i)) = l₁.get i := by
  classical
  simp [reorderPerm, listMembershipEquiv]

theorem reorderPerm_idxOf {l₁ l₂ : List V}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h : l₁.toFinset = l₂.toFinset)
    {a : V} (ha₁ : a ∈ l₁) (ha₂ : a ∈ l₂) :
    (finCongr (length_eq_of_toFinset_eq h₁ h₂ h))
        (reorderPerm h₁ h₂ h ⟨l₁.idxOf a, List.idxOf_lt_length_iff.2 ha₁⟩) =
      ⟨l₂.idxOf a, List.idxOf_lt_length_iff.2 ha₂⟩ := by
  have hget := get_reorderPerm h₁ h₂ h ⟨l₁.idxOf a, List.idxOf_lt_length_iff.2 ha₁⟩
  apply (h₂.get_inj_iff).mp
  simpa [List.idxOf_get, h₁, h₂, ha₁, ha₂] using hget

theorem finCongr_succ {m n : Nat} (h : m = n) (i : Fin m) :
    finCongr (by simpa [h]) i.succ = (finCongr h i).succ := by
  apply Fin.ext
  simp

theorem finCongr_cycleRange {m n : Nat} (h : m = n) (i j : Fin m) :
    finCongr h (i.cycleRange j) = (finCongr h i).cycleRange (finCongr h j) := by
  subst h
  rfl

theorem finCongr_cycleRange_symm {m n : Nat} (h : m = n) (i j : Fin m) :
    finCongr h (i.cycleRange.symm j) = (finCongr h i).cycleRange.symm (finCongr h j) := by
  subst h
  rfl

theorem finCongr_trans {a b c : Nat} (hab : a = b) (hbc : b = c) (i : Fin a) :
    finCongr hbc (finCongr hab i) = finCongr (hab.trans hbc) i := by
  subst hab
  subst hbc
  rfl

theorem reorderPerm_cons_apply_zero {a : V} {l₁ l₂ : List V}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h : l₁.toFinset = l₂.toFinset)
    (ha₁ : a ∉ l₁) (ha₂ : a ∉ l₂) :
    reorderPerm (List.nodup_cons.2 ⟨ha₁, h₁⟩) (List.nodup_cons.2 ⟨ha₂, h₂⟩) (by simpa [h])
        ⟨0, by simp⟩ =
      ⟨0, by simp⟩ := by
  let zeroDom : Fin ((a :: l₁).length) := ⟨0, by simp⟩
  let zeroCod : Fin ((a :: l₂).length) := ⟨0, by simp⟩
  have hzero :
      (finCongr (length_eq_of_toFinset_eq (List.nodup_cons.2 ⟨ha₁, h₁⟩) (List.nodup_cons.2 ⟨ha₂, h₂⟩)
        (by simpa [h])))
        (reorderPerm (List.nodup_cons.2 ⟨ha₁, h₁⟩) (List.nodup_cons.2 ⟨ha₂, h₂⟩) (by simpa [h])
          zeroDom) = zeroCod := by
    have ha_cons₁ : a ∈ a :: l₁ := by simp
    have ha_cons₂ : a ∈ a :: l₂ := by simp
    have hidx :=
      (reorderPerm_idxOf (List.nodup_cons.2 ⟨ha₁, h₁⟩) (List.nodup_cons.2 ⟨ha₂, h₂⟩)
        (by simpa [h]) ha_cons₁ ha_cons₂)
    simpa [zeroDom, zeroCod] using hidx
  exact (finCongr _).injective hzero

theorem reorderPerm_cons_apply_succ {a : V} {l₁ l₂ : List V}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h : l₁.toFinset = l₂.toFinset)
    (ha₁ : a ∉ l₁) (ha₂ : a ∉ l₂)
    (k : Fin l₁.length) :
    reorderPerm (List.nodup_cons.2 ⟨ha₁, h₁⟩) (List.nodup_cons.2 ⟨ha₂, h₂⟩) (by simpa [h])
        k.succ =
      (reorderPerm h₁ h₂ h k).succ := by
  let p :=
    reorderPerm (List.nodup_cons.2 ⟨ha₁, h₁⟩) (List.nodup_cons.2 ⟨ha₂, h₂⟩) (by simpa [h])
  let q := reorderPerm h₁ h₂ h
  have hlen : l₁.length = l₂.length := length_eq_of_toFinset_eq h₁ h₂ h
  let zeroDom : Fin (l₁.length + 1) := ⟨0, Nat.succ_pos _⟩
  let zeroCod : Fin (l₂.length + 1) := ⟨0, Nat.succ_pos _⟩
  have hk_ne_head : l₁.get k ≠ a := by
    intro hk
    exact ha₁ (hk ▸ List.get_mem l₁ k)
  have hp_ne_zero : p k.succ ≠ zeroDom := by
    intro hp0
    have htmp :=
      get_reorderPerm (List.nodup_cons.2 ⟨ha₁, h₁⟩) (List.nodup_cons.2 ⟨ha₂, h₂⟩)
        (by simpa [h]) k.succ
    rw [hp0] at htmp
    have hhead : a = l₁.get k := by
      simpa [zeroCod, zeroDom, p] using htmp
    exact hk_ne_head hhead.symm
  rcases Fin.eq_zero_or_eq_succ (p k.succ) with hp0 | ⟨j, hj⟩
  · exact (hp_ne_zero hp0).elim
  have hget_j : l₂.get (finCongr hlen j) = l₁.get k := by
    have htmp :=
      get_reorderPerm (List.nodup_cons.2 ⟨ha₁, h₁⟩) (List.nodup_cons.2 ⟨ha₂, h₂⟩)
        (by simpa [h]) k.succ
    rw [hj] at htmp
    simpa [finCongr_succ, p] using htmp
  have hget_q : l₂.get (finCongr hlen (q k)) = l₁.get k := by
    simpa [q] using get_reorderPerm h₁ h₂ h k
  have hjq_cast : finCongr hlen j = finCongr hlen (q k) := by
    exact (h₂.get_inj_iff).mp (hget_j.trans hget_q.symm)
  have hjq : j = q k := by
    exact (finCongr hlen).injective hjq_cast
  apply Fin.ext
  calc
    (p k.succ).1 = (j.succ).1 := by
      exact congrArg Fin.val hj
    _ = ((q k).succ).1 := by
      simp [hjq]

theorem reorderPerm_cons_eq_decomposeFin_symm {a : V} {l₁ l₂ : List V}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h : l₁.toFinset = l₂.toFinset)
    (ha₁ : a ∉ l₁) (ha₂ : a ∉ l₂) :
    reorderPerm (List.nodup_cons.2 ⟨ha₁, h₁⟩) (List.nodup_cons.2 ⟨ha₂, h₂⟩) (by simpa [h]) =
      Equiv.Perm.decomposeFin.symm (⟨0, by simp⟩, reorderPerm h₁ h₂ h) := by
  ext i
  refine Fin.cases ?_ ?_ i
  · have hz := reorderPerm_cons_apply_zero h₁ h₂ h ha₁ ha₂
    simpa using hz
  · intro k
    exact congrArg Fin.val (reorderPerm_cons_apply_succ h₁ h₂ h ha₁ ha₂ k)

theorem sign_reorderPerm_cons {a : V} {l₁ l₂ : List V}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h : l₁.toFinset = l₂.toFinset)
    (ha₁ : a ∉ l₁) (ha₂ : a ∉ l₂) :
    Equiv.Perm.sign
        (reorderPerm (List.nodup_cons.2 ⟨ha₁, h₁⟩) (List.nodup_cons.2 ⟨ha₂, h₂⟩) (by simpa [h])) =
      Equiv.Perm.sign (reorderPerm h₁ h₂ h) := by
  rw [reorderPerm_cons_eq_decomposeFin_symm h₁ h₂ h ha₁ ha₂]
  simp

theorem get_cons_eraseIdx_cycleRange_symm {l : List V} {n : Nat} (hlen : l.length = n + 1)
    (j k : Fin (n + 1)) :
    (l[j] :: l.eraseIdx j)[k]'(by
      have hlen' : (l.eraseIdx ↑j).length = n := by
        rw [List.length_eraseIdx_of_lt]
        · omega
        · simpa [hlen] using j.is_lt
      simpa [hlen'] using k.is_lt) =
      l[j.cycleRange.symm k]'(by simpa [hlen] using (j.cycleRange.symm k).is_lt) := by
  have hlen' : (l.eraseIdx ↑j).length = n := by
    rw [List.length_eraseIdx_of_lt]
    · omega
    · simpa [hlen] using j.is_lt
  refine Fin.cases ?_ ?_ k
  · simp [hlen', Fin.cycleRange_symm_zero]
  · intro i
    simpa [hlen', Fin.cycleRange_symm_succ] using getElem_eraseIdx_fin (l := l) hlen j i

private theorem nodup_cons_get_eraseIdx {l : List V} (hl : l.Nodup) (j : Fin l.length) :
    (l.get j :: l.eraseIdx j).Nodup := by
  simpa using (List.getElem_cons_eraseIdx_perm (l := l) j.is_lt).nodup_iff.2 hl

private theorem toFinset_cons_get_eraseIdx {l : List V} (j : Fin l.length) :
    (l.get j :: l.eraseIdx j).toFinset = l.toFinset := by
  let hperm := List.getElem_cons_eraseIdx_perm (l := l) j.is_lt
  ext x
  constructor
  · intro hx
    have hx' : x ∈ l.get j :: l.eraseIdx j := by simpa using hx
    exact by simpa using hperm.subset hx'
  · intro hx
    have hx' : x ∈ l := by simpa using hx
    exact by simpa using hperm.symm.subset hx'

private theorem length_eq_cons_get_eraseIdx {l : List V} (hl : l.Nodup) (j : Fin l.length) :
    length_eq_of_toFinset_eq (nodup_cons_get_eraseIdx hl j) hl (toFinset_cons_get_eraseIdx j) =
      by
        rw [List.length_cons, List.length_eraseIdx_of_lt]
        · simpa using (Nat.succ_pred_eq_of_pos (Nat.zero_lt_of_lt j.is_lt))
        · exact j.is_lt := by
  apply Subsingleton.elim

theorem reorderPerm_cons_get_eraseIdx_eq_cycleRange_symm {l : List V}
    (hl : l.Nodup) (j : Fin l.length) :
    Equiv.permCongr
        (finCongr (length_eq_of_toFinset_eq (nodup_cons_get_eraseIdx hl j) hl
          (toFinset_cons_get_eraseIdx j)))
        (reorderPerm (nodup_cons_get_eraseIdx hl j) hl (toFinset_cons_get_eraseIdx j)) =
      j.cycleRange.symm := by
  ext k
  let hmovedLen :=
    length_eq_of_toFinset_eq (nodup_cons_get_eraseIdx hl j) hl (toFinset_cons_get_eraseIdx j)
  let k' : Fin (l.get j :: l.eraseIdx j).length := (finCongr hmovedLen).symm k
  have hget :=
    get_reorderPerm (nodup_cons_get_eraseIdx hl j) hl (toFinset_cons_get_eraseIdx j) k'
  have hlen' : l.length = (l.length - 1) + 1 := by
    simpa [Nat.add_comm] using (Nat.succ_pred_eq_of_pos (Nat.zero_lt_of_lt j.is_lt)).symm
  have htarget :
      (l.get j :: l.eraseIdx j).get k' = l.get (j.cycleRange.symm k) := by
    have hbase :
        (l.get j :: l.eraseIdx j).get k' =
          l.get
            (finCongr hlen'.symm
              ((finCongr hlen' j).cycleRange.symm (finCongr hlen' k))) := by
      simpa [k', hmovedLen, length_eq_cons_get_eraseIdx hl j, hlen'] using
        (get_cons_eraseIdx_cycleRange_symm (l := l) (n := l.length - 1) hlen'
          (j := finCongr hlen' j) (k := finCongr hlen' k))
    have hidx :
        finCongr hlen'.symm ((finCongr hlen' j).cycleRange.symm (finCongr hlen' k)) =
          j.cycleRange.symm k := by
      apply (finCongr hlen').injective
      simpa using (finCongr_cycleRange_symm hlen' j k).symm
    convert hbase using 1
    exact congrArg (fun t => l.get t) hidx.symm
  apply congrArg Fin.val
  exact (hl.get_inj_iff).mp <| by
    simpa [Equiv.permCongr_apply, hmovedLen, k'] using hget.trans htarget

theorem sign_reorderPerm_cons_get_eraseIdx {l : List V}
    (hl : l.Nodup) (j : Fin l.length) :
    Equiv.Perm.sign
        (reorderPerm (nodup_cons_get_eraseIdx hl j) hl (toFinset_cons_get_eraseIdx j)) =
      (-1 : ℤˣ) ^ (j : ℕ) := by
  let hmovedLen :=
    length_eq_of_toFinset_eq (nodup_cons_get_eraseIdx hl j) hl (toFinset_cons_get_eraseIdx j)
  rw [← Equiv.Perm.sign_permCongr (finCongr hmovedLen)
      (reorderPerm (nodup_cons_get_eraseIdx hl j) hl (toFinset_cons_get_eraseIdx j))]
  rw [reorderPerm_cons_get_eraseIdx_eq_cycleRange_symm (hl := hl) (j := j)]
  simp

theorem reorderPerm_trans {l₁ l₂ l₃ : List V}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h₃ : l₃.Nodup)
    (h₁₂ : l₁.toFinset = l₂.toFinset) (h₂₃ : l₂.toFinset = l₃.toFinset) :
    (reorderPerm h₁ h₂ h₁₂).trans
        (Equiv.permCongr (finCongr (length_eq_of_toFinset_eq h₁ h₂ h₁₂)).symm
          (reorderPerm h₂ h₃ h₂₃)) =
      reorderPerm h₁ h₃ (h₁₂.trans h₂₃) := by
  ext i
  let h12len := length_eq_of_toFinset_eq h₁ h₂ h₁₂
  let h23len := length_eq_of_toFinset_eq h₂ h₃ h₂₃
  let h13len := length_eq_of_toFinset_eq h₁ h₃ (h₁₂.trans h₂₃)
  have h12 := get_reorderPerm h₁ h₂ h₁₂ i
  have h23 :=
    get_reorderPerm h₂ h₃ h₂₃
      ((finCongr h12len) (reorderPerm h₁ h₂ h₁₂ i))
  have hcomp :
      l₃.get
          (finCongr h13len
            (((reorderPerm h₁ h₂ h₁₂).trans
              (Equiv.permCongr (finCongr h12len).symm (reorderPerm h₂ h₃ h₂₃))) i)) =
        l₁.get i := by
    calc
      l₃.get
          (finCongr h13len
            (((reorderPerm h₁ h₂ h₁₂).trans
              (Equiv.permCongr (finCongr h12len).symm (reorderPerm h₂ h₃ h₂₃))) i)) =
        l₃.get (finCongr h23len (reorderPerm h₂ h₃ h₂₃ ((finCongr h12len) (reorderPerm h₁ h₂ h₁₂ i)))) := by
          have hcast :
              finCongr h13len
                  (((reorderPerm h₁ h₂ h₁₂).trans
                    (Equiv.permCongr (finCongr h12len).symm (reorderPerm h₂ h₃ h₂₃))) i) =
                finCongr h23len
                  (reorderPerm h₂ h₃ h₂₃ ((finCongr h12len) (reorderPerm h₁ h₂ h₁₂ i))) := by
            rw [Equiv.trans_apply, Equiv.permCongr_apply]
            simp
          exact congrArg (fun t => l₃.get t) hcast
      _ = l₂.get ((finCongr h12len) (reorderPerm h₁ h₂ h₁₂ i)) := h23
      _ = l₁.get i := h12
  have h13 := get_reorderPerm h₁ h₃ (h₁₂.trans h₂₃) i
  exact congrArg Fin.val <|
    (finCongr h13len).injective ((h₃.get_inj_iff).mp (hcomp.trans h13.symm))

private theorem toFinset_eraseIdx_eq_of_get_eq {l₁ l₂ : List V}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h : l₁.toFinset = l₂.toFinset)
    {j₁ : Fin l₁.length} {j₂ : Fin l₂.length}
    (hget : l₁.get j₁ = l₂.get j₂) :
    (l₁.eraseIdx ↑j₁).toFinset = (l₂.eraseIdx ↑j₂).toFinset := by
  let a := l₂.get j₂
  let l₁' := l₁.eraseIdx ↑j₁
  let l₂' := l₂.eraseIdx ↑j₂
  have hcons₁ : a :: l₁' = l₁.get j₁ :: l₁.eraseIdx ↑j₁ := by
    simpa [l₁'] using congrArg (fun x => x :: l₁') hget.symm
  have hmoved₁ : (a :: l₁').toFinset = l₁.toFinset := by
    exact hcons₁ ▸ toFinset_cons_get_eraseIdx j₁
  have hmoved₂ : (a :: l₂').toFinset = l₂.toFinset := by
    simpa [a, l₂'] using toFinset_cons_get_eraseIdx j₂
  have hmovedN₁ : (a :: l₁').Nodup := by
    exact hcons₁ ▸ nodup_cons_get_eraseIdx h₁ j₁
  have hmovedN₂ : (a :: l₂').Nodup := by
    simpa [a, l₂'] using nodup_cons_get_eraseIdx h₂ j₂
  have hMoved : (a :: l₁').toFinset = (a :: l₂').toFinset := by
    exact (hmoved₁.trans h).trans hmoved₂.symm
  simpa [a, l₁', l₂'] using (toFinset_tail_eq_erase (a := a) hmovedN₁ hmovedN₂ hMoved)

theorem sign_reorderPerm_eraseIdx_of_get_eq {l₁ l₂ : List V}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h : l₁.toFinset = l₂.toFinset)
    {j₁ : Fin l₁.length} {j₂ : Fin l₂.length}
    (hget : l₁.get j₁ = l₂.get j₂) :
    Equiv.Perm.sign
        (reorderPerm
          (h₁.sublist (List.eraseIdx_sublist l₁ ↑j₁))
          (h₂.sublist (List.eraseIdx_sublist l₂ ↑j₂))
          (toFinset_eraseIdx_eq_of_get_eq h₁ h₂ h hget)) =
      Equiv.Perm.sign (reorderPerm h₁ h₂ h) *
        ((-1 : ℤˣ) ^ (j₁ : ℕ)) *
        ((-1 : ℤˣ) ^ (j₂ : ℕ)) := by
  let a := l₂.get j₂
  let l₁' := l₁.eraseIdx ↑j₁
  let l₂' := l₂.eraseIdx ↑j₂
  have hcons₁ : a :: l₁' = l₁.get j₁ :: l₁.eraseIdx ↑j₁ := by
    simpa [l₁'] using congrArg (fun x => x :: l₁') hget.symm
  let hmoved₁ : (a :: l₁').toFinset = l₁.toFinset := by
    exact hcons₁ ▸ toFinset_cons_get_eraseIdx j₁
  let hmoved₂ : (a :: l₂').toFinset = l₂.toFinset := by
    simpa [a, l₂'] using toFinset_cons_get_eraseIdx j₂
  let h₁' : l₁'.Nodup := h₁.sublist (List.eraseIdx_sublist l₁ ↑j₁)
  let h₂' : l₂'.Nodup := h₂.sublist (List.eraseIdx_sublist l₂ ↑j₂)
  let hmovedN₁ : (a :: l₁').Nodup := by
    exact hcons₁ ▸ nodup_cons_get_eraseIdx h₁ j₁
  let hmovedN₂ : (a :: l₂').Nodup := by
    simpa [a, l₂'] using nodup_cons_get_eraseIdx h₂ j₂
  let hMoved : (a :: l₁').toFinset = (a :: l₂').toFinset := by
    exact (hmoved₁.trans h).trans hmoved₂.symm
  let hTail : l₁'.toFinset = l₂'.toFinset :=
    toFinset_eraseIdx_eq_of_get_eq h₁ h₂ h hget
  have hCons :
      Equiv.Perm.sign (reorderPerm hmovedN₁ hmovedN₂ hMoved) =
        Equiv.Perm.sign (reorderPerm h₁' h₂' hTail) := by
    simpa [a, l₁', l₂', h₁', h₂', hTail] using
      (sign_reorderPerm_cons h₁' h₂' hTail
        (ha₁ := (List.nodup_cons.mp hmovedN₁).1)
        (ha₂ := (List.nodup_cons.mp hmovedN₂).1))
  have hMovedToL₂ :
      Equiv.Perm.sign (reorderPerm hmovedN₁ h₂ (hmoved₁.trans h)) =
        Equiv.Perm.sign (reorderPerm h₁ h₂ h) *
          ((-1 : ℤˣ) ^ (j₁ : ℕ)) := by
    have hsHead₁ :
        Equiv.Perm.sign (reorderPerm hmovedN₁ h₁ hmoved₁) = (-1 : ℤˣ) ^ (j₁ : ℕ) := by
      have hpermHead :
          reorderPerm hmovedN₁ h₁ hmoved₁ =
            reorderPerm (nodup_cons_get_eraseIdx h₁ j₁) h₁ (toFinset_cons_get_eraseIdx j₁) := by
        ext i
        let p₁ := reorderPerm hmovedN₁ h₁ hmoved₁
        let p₂ := reorderPerm (nodup_cons_get_eraseIdx h₁ j₁) h₁ (toFinset_cons_get_eraseIdx j₁)
        let hlen₁ := length_eq_of_toFinset_eq hmovedN₁ h₁ hmoved₁
        let hlen₂ := length_eq_of_toFinset_eq (nodup_cons_get_eraseIdx h₁ j₁) h₁ (toFinset_cons_get_eraseIdx j₁)
        have hg₁ := get_reorderPerm hmovedN₁ h₁ hmoved₁ i
        have hg₂ := get_reorderPerm (nodup_cons_get_eraseIdx h₁ j₁) h₁ (toFinset_cons_get_eraseIdx j₁) i
        have hsrc : (a :: l₁').get i = (l₁.get j₁ :: l₁.eraseIdx ↑j₁).get i := by
          simpa [hcons₁]
        have hcast :
            (finCongr hlen₁) (p₁ i) = (finCongr hlen₂) (p₂ i) := by
          apply (h₁.get_inj_iff).mp
          exact hg₁.trans (hsrc.trans hg₂.symm)
        simpa using congrArg Fin.val hcast
      rw [hpermHead]
      exact sign_reorderPerm_cons_get_eraseIdx (hl := h₁) (j := j₁)
    calc
      Equiv.Perm.sign (reorderPerm hmovedN₁ h₂ (hmoved₁.trans h)) =
        Equiv.Perm.sign
          ((reorderPerm hmovedN₁ h₁ hmoved₁).trans
            (Equiv.permCongr (finCongr (length_eq_of_toFinset_eq
              hmovedN₁ h₁ hmoved₁)).symm
              (reorderPerm h₁ h₂ h))) := by
            rw [reorderPerm_trans hmovedN₁ h₁ h₂ hmoved₁ h]
      _ = Equiv.Perm.sign (reorderPerm h₁ h₂ h) *
            Equiv.Perm.sign (reorderPerm hmovedN₁ h₁ hmoved₁) := by
            rw [Equiv.Perm.sign_trans, Equiv.Perm.sign_permCongr]
      _ = Equiv.Perm.sign (reorderPerm h₁ h₂ h) * ((-1 : ℤˣ) ^ (j₁ : ℕ)) := by
            rw [hsHead₁]
  have hMovedToL₂' :
      Equiv.Perm.sign (reorderPerm hmovedN₁ h₂ (hMoved.trans hmoved₂)) =
        Equiv.Perm.sign (reorderPerm h₁ h₂ h) *
          ((-1 : ℤˣ) ^ (j₁ : ℕ)) := by
    have hproof : hMoved.trans hmoved₂ = hmoved₁.trans h := by
      apply Subsingleton.elim
    simpa [hproof] using hMovedToL₂
  have hMovedCompareRaw :
      Equiv.Perm.sign (reorderPerm hmovedN₁ h₂ (hMoved.trans hmoved₂)) =
        Equiv.Perm.sign (reorderPerm hmovedN₂ h₂ hmoved₂) *
          Equiv.Perm.sign (reorderPerm hmovedN₁ hmovedN₂ hMoved) := by
    calc
      Equiv.Perm.sign (reorderPerm hmovedN₁ h₂ (hMoved.trans hmoved₂)) =
        Equiv.Perm.sign
          (((reorderPerm hmovedN₁ hmovedN₂ hMoved).trans
            (Equiv.permCongr (finCongr (length_eq_of_toFinset_eq
              hmovedN₁ hmovedN₂ hMoved)).symm
              (reorderPerm hmovedN₂ h₂ hmoved₂)))) := by
            rw [reorderPerm_trans
              hmovedN₁
              hmovedN₂
              h₂
              hMoved
              hmoved₂]
      _ =
        Equiv.Perm.sign (reorderPerm hmovedN₂ h₂ hmoved₂) *
          Equiv.Perm.sign (reorderPerm hmovedN₁ hmovedN₂ hMoved) := by
            rw [Equiv.Perm.sign_trans, Equiv.Perm.sign_permCongr]
  have hMovedCompare :
      Equiv.Perm.sign (reorderPerm hmovedN₁ hmovedN₂ hMoved) =
        Equiv.Perm.sign (reorderPerm hmovedN₂ h₂ hmoved₂) *
          Equiv.Perm.sign (reorderPerm h₁ h₂ h) *
          ((-1 : ℤˣ) ^ (j₁ : ℕ)) := by
    calc
      Equiv.Perm.sign (reorderPerm hmovedN₁ hmovedN₂ hMoved) =
        Equiv.Perm.sign (reorderPerm hmovedN₂ h₂ hmoved₂) *
          (Equiv.Perm.sign (reorderPerm hmovedN₂ h₂ hmoved₂) *
            Equiv.Perm.sign (reorderPerm hmovedN₁ hmovedN₂ hMoved)) := by
            rw [← mul_assoc, Int.units_mul_self, one_mul]
      _ =
        Equiv.Perm.sign (reorderPerm hmovedN₂ h₂ hmoved₂) *
          Equiv.Perm.sign (reorderPerm hmovedN₁ h₂ (hMoved.trans hmoved₂)) := by
            rw [hMovedCompareRaw]
      _ =
        Equiv.Perm.sign (reorderPerm hmovedN₂ h₂ hmoved₂) *
          (Equiv.Perm.sign (reorderPerm h₁ h₂ h) * ((-1 : ℤˣ) ^ (j₁ : ℕ))) := by
            rw [hMovedToL₂']
      _ =
        Equiv.Perm.sign (reorderPerm hmovedN₂ h₂ hmoved₂) *
          Equiv.Perm.sign (reorderPerm h₁ h₂ h) *
          ((-1 : ℤˣ) ^ (j₁ : ℕ)) := by
            simp [mul_assoc]
  calc
    Equiv.Perm.sign (reorderPerm h₁' h₂' hTail) =
      Equiv.Perm.sign (reorderPerm hmovedN₁ hmovedN₂ hMoved) := by
          simpa [hCons] using hCons.symm
    _ =
      Equiv.Perm.sign (reorderPerm hmovedN₂ h₂ hmoved₂) *
        Equiv.Perm.sign (reorderPerm h₁ h₂ h) *
        ((-1 : ℤˣ) ^ (j₁ : ℕ)) := hMovedCompare
    _ =
      ((-1 : ℤˣ) ^ (j₂ : ℕ)) *
        Equiv.Perm.sign (reorderPerm h₁ h₂ h) *
        ((-1 : ℤˣ) ^ (j₁ : ℕ)) := by
          simpa [a, l₂'] using sign_reorderPerm_cons_get_eraseIdx (hl := h₂) (j := j₂)
    _ =
      Equiv.Perm.sign (reorderPerm h₁ h₂ h) *
        ((-1 : ℤˣ) ^ (j₁ : ℕ)) *
        ((-1 : ℤˣ) ^ (j₂ : ℕ)) := by
          simp [mul_assoc, mul_left_comm, mul_comm]

noncomputable def orderComparisonSign (o : Orientation K) (σ : K.Simplex) (l : List V)
    (hN : l.Nodup) (hSet : l.toFinset = σ.1) : ℤ :=
  let hEq : (o.orderedVertices σ).toFinset = l.toFinset := (o.toFinset_eq σ).trans hSet.symm
  ((Equiv.Perm.sign (reorderPerm (o.nodup σ) hN hEq) : ℤˣ) : ℤ)

private theorem orderComparisonSign_congr (o : Orientation K) (σ : K.Simplex)
    {l₁ l₂ : List V} (heq : l₁ = l₂)
    (hN₁ : l₁.Nodup) (hN₂ : l₂.Nodup)
    (hSet₁ : l₁.toFinset = σ.1) (hSet₂ : l₂.toFinset = σ.1) :
    orderComparisonSign o σ l₁ hN₁ hSet₁ =
      orderComparisonSign o σ l₂ hN₂ hSet₂ := by
  subst heq
  rfl

noncomputable def orientationSimplexSignUnit (o₁ o₂ : Orientation K) (σ : K.Simplex) : ℤˣ :=
  Equiv.Perm.sign
    (reorderPerm (o₁.nodup σ) (o₂.nodup σ)
      ((o₁.toFinset_eq σ).trans (o₂.toFinset_eq σ).symm))

noncomputable def orientationSimplexSign (o₁ o₂ : Orientation K) (σ : K.Simplex) : ℤ :=
  (orientationSimplexSignUnit o₁ o₂ σ : ℤ)

theorem orderComparisonSign_eq_orientationSimplexSign_mul
    (o₁ o₂ : Orientation K) (σ : K.Simplex) (l : List V)
    (hN : l.Nodup) (hSet : l.toFinset = σ.1) :
    orderComparisonSign o₁ σ l hN hSet =
      orderComparisonSign o₂ σ l hN hSet * orientationSimplexSign o₁ o₂ σ := by
  let h₁₂ : (o₁.orderedVertices σ).toFinset = (o₂.orderedVertices σ).toFinset :=
    (o₁.toFinset_eq σ).trans (o₂.toFinset_eq σ).symm
  let h₂₃ : (o₂.orderedVertices σ).toFinset = l.toFinset :=
    (o₂.toFinset_eq σ).trans hSet.symm
  unfold orderComparisonSign orientationSimplexSign orientationSimplexSignUnit
  calc
    ((Equiv.Perm.sign
        (reorderPerm (o₁.nodup σ) hN ((o₁.toFinset_eq σ).trans hSet.symm)) : ℤˣ) : ℤ) =
      ((Equiv.Perm.sign
          ((reorderPerm (o₁.nodup σ) (o₂.nodup σ) h₁₂).trans
            (Equiv.permCongr
              (finCongr (length_eq_of_toFinset_eq (o₁.nodup σ) (o₂.nodup σ) h₁₂)).symm
              (reorderPerm (o₂.nodup σ) hN h₂₃))) : ℤˣ) : ℤ) := by
            rw [reorderPerm_trans (o₁.nodup σ) (o₂.nodup σ) hN h₁₂ h₂₃]
    _ =
      ((Equiv.Perm.sign (reorderPerm (o₂.nodup σ) hN h₂₃) *
          Equiv.Perm.sign (reorderPerm (o₁.nodup σ) (o₂.nodup σ) h₁₂) : ℤˣ) : ℤ) := by
            rw [Equiv.Perm.sign_trans, Equiv.Perm.sign_permCongr]
    _ =
      orderComparisonSign o₂ σ l hN hSet *
        orientationSimplexSign o₁ o₂ σ := by
            rfl

theorem orderComparisonSign_eq_reorderPerm_mul
    (o : Orientation K) (σ : K.Simplex) (l₁ l₂ : List V)
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hSet₁ : l₁.toFinset = σ.1) (hSet₂ : l₂.toFinset = σ.1) :
    orderComparisonSign o σ l₁ h₁ hSet₁ =
      ((Equiv.Perm.sign (reorderPerm h₂ h₁ (hSet₂.trans hSet₁.symm)) : ℤˣ) : ℤ) *
        orderComparisonSign o σ l₂ h₂ hSet₂ := by
  let h₀₂ : (o.orderedVertices σ).toFinset = l₂.toFinset :=
    (o.toFinset_eq σ).trans hSet₂.symm
  let h₂₁ : l₂.toFinset = l₁.toFinset := hSet₂.trans hSet₁.symm
  unfold orderComparisonSign
  calc
    ((Equiv.Perm.sign (reorderPerm (o.nodup σ) h₁ ((o.toFinset_eq σ).trans hSet₁.symm)) : ℤˣ) : ℤ) =
      ((Equiv.Perm.sign
          ((reorderPerm (o.nodup σ) h₂ h₀₂).trans
            (Equiv.permCongr
              (finCongr (length_eq_of_toFinset_eq (o.nodup σ) h₂ h₀₂)).symm
              (reorderPerm h₂ h₁ h₂₁))) : ℤˣ) : ℤ) := by
            rw [reorderPerm_trans (o.nodup σ) h₂ h₁ h₀₂ h₂₁]
    _ =
      ((Equiv.Perm.sign (reorderPerm h₂ h₁ h₂₁) *
          Equiv.Perm.sign (reorderPerm (o.nodup σ) h₂ h₀₂) : ℤˣ) : ℤ) := by
            rw [Equiv.Perm.sign_trans, Equiv.Perm.sign_permCongr]
    _ =
      ((Equiv.Perm.sign (reorderPerm h₂ h₁ (hSet₂.trans hSet₁.symm)) : ℤˣ) : ℤ) *
        orderComparisonSign o σ l₂ h₂ hSet₂ := by
            rfl

/-- Signed incidence relation `[σ : τ]` for codimension-1 face relations. -/
noncomputable def signedIncidence (o : Orientation K) {σ τ : K.Simplex} (hστ : σ ≤ τ) : ℤ :=
  let deleted := τ.1 \ σ.1
  match deleted.toList with
  | [v] =>
      Orientation.alternatingSign ((o.orderedVertices τ).idxOf v) *
        orderComparisonSign o σ (inducedFaceVertices o hστ)
          (inducedFaceVertices_nodup o hστ) (inducedFaceVertices_toFinset o hστ)
  | _ => 0

private theorem deleted_singleton_data {σ τ : K.Simplex} {v : V}
    (hv : (τ.1 \ σ.1).toList = [v]) :
    v ∈ τ.1 ∧ v ∉ σ.1 ∧ ∀ w, w ∈ τ.1 → w ≠ v → w ∈ σ.1 := by
  have hvmem : v ∈ (τ.1 \ σ.1).toList := by
    simpa [hv]
  have hvdiff : v ∈ τ.1 \ σ.1 := by
    simpa using hvmem
  let hvdiff' := Finset.mem_sdiff.mp hvdiff
  refine ⟨hvdiff'.1, hvdiff'.2, ?_⟩
  intro w hwτ hwv
  by_contra hwσ
  have hwdiff : w ∈ τ.1 \ σ.1 := Finset.mem_sdiff.mpr ⟨hwτ, hwσ⟩
  have : w = v := by
    simpa [hv] using (show w ∈ (τ.1 \ σ.1).toList by simpa using hwdiff)
  exact hwv this

theorem deleted_toList_eq_singleton_of_card_succ {σ τ : K.Simplex}
    (hστ : σ ≤ τ) (hcard : τ.1.card = σ.1.card + 1) :
    ∃ v, (τ.1 \ σ.1).toList = [v] := by
  have hdiff : (τ.1 \ σ.1).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hστ]
    omega
  rcases Finset.card_eq_one.mp hdiff with ⟨v, hv⟩
  refine ⟨v, ?_⟩
  rw [hv]
  simp

theorem deleted_toList_eq_singleton_of_qface {q : Nat}
    {σ : K.qSimplices q} {τ : K.qSimplices (q + 1)} (hστ : σ.1 ≤ τ.1) :
    ∃ v, (τ.1.1 \ σ.1.1).toList = [v] := by
  have hcard : τ.1.1.card = σ.1.1.card + 1 := by
    rw [show τ.1.1.card = q + 2 by
      simpa [SimplicialComplex.qSimplices] using
        (SimplicialComplex.mem_qSimplices (K := K) (σ := τ.1) (q := q + 1)).mp τ.2]
    rw [show σ.1.1.card = q + 1 by
      simpa [SimplicialComplex.qSimplices] using
        (SimplicialComplex.mem_qSimplices (K := K) (σ := σ.1) (q := q)).mp σ.2]
  exact deleted_toList_eq_singleton_of_card_succ (σ := σ.1) (τ := τ.1) hστ hcard

theorem signedIncidence_eq_orientationSimplexSign_mul
    (o₁ o₂ : Orientation K) {σ τ : K.Simplex} (hστ : σ ≤ τ) {v : V}
    (hv : (τ.1 \ σ.1).toList = [v]) :
    signedIncidence o₁ hστ =
      orientationSimplexSign o₁ o₂ τ *
        orientationSimplexSign o₁ o₂ σ *
        signedIncidence o₂ hστ := by
  have ⟨hvτ, hvσ, hrest⟩ := deleted_singleton_data (σ := σ) (τ := τ) hv
  let l₁ := o₁.orderedVertices τ
  let l₂ := o₂.orderedVertices τ
  have hv₁ : v ∈ l₁ := by
    have hmem : v ∈ (o₁.orderedVertices τ).toFinset := by
      simpa [o₁.toFinset_eq τ] using hvτ
    simpa [l₁] using hmem
  have hv₂ : v ∈ l₂ := by
    have hmem : v ∈ (o₂.orderedVertices τ).toFinset := by
      simpa [o₂.toFinset_eq τ] using hvτ
    simpa [l₂] using hmem
  let j₁ : Fin l₁.length := ⟨l₁.idxOf v, List.idxOf_lt_length_iff.2 hv₁⟩
  let j₂ : Fin l₂.length := ⟨l₂.idxOf v, List.idxOf_lt_length_iff.2 hv₂⟩
  have hget₁ : l₁.get j₁ = v := by
    simpa [l₁, j₁] using
      (List.idxOf_get (a := v) (l := l₁) (h := List.idxOf_lt_length_iff.2 hv₁))
  have hget₂ : l₂.get j₂ = v := by
    simpa [l₂, j₂] using
      (List.idxOf_get (a := v) (l := l₂) (h := List.idxOf_lt_length_iff.2 hv₂))
  have hget : l₁.get j₁ = l₂.get j₂ := by
    rw [hget₁, hget₂]
  let e₁ := l₁.eraseIdx ↑j₁
  let e₂ := l₂.eraseIdx ↑j₂
  let hN₁ : e₁.Nodup := (o₁.nodup τ).sublist (List.eraseIdx_sublist l₁ ↑j₁)
  let hN₂ : e₂.Nodup := (o₂.nodup τ).sublist (List.eraseIdx_sublist l₂ ↑j₂)
  have hind₁ : inducedFaceVertices o₁ hστ = e₁ := by
    rw [inducedFaceVertices_eq_erase_of_codim1 o₁ hστ hvτ hvσ hrest]
    simpa [l₁, e₁, j₁, hget₁] using (o₁.nodup τ).erase_get j₁
  have hind₂ : inducedFaceVertices o₂ hστ = e₂ := by
    rw [inducedFaceVertices_eq_erase_of_codim1 o₂ hστ hvτ hvσ hrest]
    simpa [l₂, e₂, j₂, hget₂] using (o₂.nodup τ).erase_get j₂
  have hSet₁ : e₁.toFinset = σ.1 := by
    rw [← hind₁]
    exact inducedFaceVertices_toFinset o₁ hστ
  have hSet₂ : e₂.toFinset = σ.1 := by
    rw [← hind₂]
    exact inducedFaceVertices_toFinset o₂ hστ
  have hτset : l₁.toFinset = l₂.toFinset := by
    exact (o₁.toFinset_eq τ).trans (o₂.toFinset_eq τ).symm
  let hErase :
      e₁.toFinset = e₂.toFinset :=
    toFinset_eraseIdx_eq_of_get_eq (o₁.nodup τ) (o₂.nodup τ) hτset hget
  have hCompare₂ :
      orderComparisonSign o₂ σ e₂ hN₂ hSet₂ =
        ((Equiv.Perm.sign (reorderPerm hN₁ hN₂ hErase) : ℤˣ) : ℤ) *
          orderComparisonSign o₂ σ e₁ hN₁ hSet₁ := by
    have hproof : hSet₁.trans hSet₂.symm = hErase := by
      apply Subsingleton.elim
    simpa [hproof] using
      (orderComparisonSign_eq_reorderPerm_mul
        (o := o₂) (σ := σ) (l₁ := e₂) (l₂ := e₁) hN₂ hN₁ hSet₂ hSet₁)
  have hSignSq :
      (((Equiv.Perm.sign (reorderPerm hN₁ hN₂ hErase) : ℤˣ) : ℤ) *
          ((Equiv.Perm.sign (reorderPerm hN₁ hN₂ hErase) : ℤˣ) : ℤ)) = 1 := by
    change (((Equiv.Perm.sign (reorderPerm hN₁ hN₂ hErase) : ℤˣ) *
        Equiv.Perm.sign (reorderPerm hN₁ hN₂ hErase) : ℤˣ) : ℤ) = 1
    rw [Int.units_mul_self]
    simp
  have hCompare₁ :
      orderComparisonSign o₂ σ e₁ hN₁ hSet₁ =
        ((Equiv.Perm.sign (reorderPerm hN₁ hN₂ hErase) : ℤˣ) : ℤ) *
          orderComparisonSign o₂ σ e₂ hN₂ hSet₂ := by
    calc
      orderComparisonSign o₂ σ e₁ hN₁ hSet₁ =
          ((((Equiv.Perm.sign (reorderPerm hN₁ hN₂ hErase) : ℤˣ) : ℤ) *
              ((Equiv.Perm.sign (reorderPerm hN₁ hN₂ hErase) : ℤˣ) : ℤ))) *
            orderComparisonSign o₂ σ e₁ hN₁ hSet₁ := by
              rw [hSignSq, one_mul]
      _ =
          ((Equiv.Perm.sign (reorderPerm hN₁ hN₂ hErase) : ℤˣ) : ℤ) *
            (((Equiv.Perm.sign (reorderPerm hN₁ hN₂ hErase) : ℤˣ) : ℤ) *
              orderComparisonSign o₂ σ e₁ hN₁ hSet₁) := by
              ring
      _ =
          ((Equiv.Perm.sign (reorderPerm hN₁ hN₂ hErase) : ℤˣ) : ℤ) *
            orderComparisonSign o₂ σ e₂ hN₂ hSet₂ := by
              rw [hCompare₂]
  have hσCompare :
      orderComparisonSign o₁ σ e₁ hN₁ hSet₁ =
        ((Equiv.Perm.sign (reorderPerm hN₁ hN₂ hErase) : ℤˣ) : ℤ) *
          orderComparisonSign o₂ σ e₂ hN₂ hSet₂ *
          orientationSimplexSign o₁ o₂ σ := by
    rw [orderComparisonSign_eq_orientationSimplexSign_mul
      (o₁ := o₁) (o₂ := o₂) (σ := σ) (l := e₁) (hN := hN₁) (hSet := hSet₁)]
    rw [hCompare₁]
  have hEraseSign :
      ((Equiv.Perm.sign (reorderPerm hN₁ hN₂ hErase) : ℤˣ) : ℤ) =
        orientationSimplexSign o₁ o₂ τ *
          Orientation.alternatingSign (j₁ : ℕ) *
          Orientation.alternatingSign (j₂ : ℕ) := by
    simpa [orientationSimplexSign, orientationSimplexSignUnit,
      alternatingSign_eq_neg_one_pow, l₁, l₂, e₁, e₂, hN₁, hN₂, hErase,
      mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun u : ℤˣ => (u : ℤ))
        (sign_reorderPerm_eraseIdx_of_get_eq
          (h₁ := o₁.nodup τ) (h₂ := o₂.nodup τ) (h := hτset)
          (j₁ := j₁) (j₂ := j₂) hget)
  have hs₁ :
      signedIncidence o₁ hστ =
        Orientation.alternatingSign (l₁.idxOf v) *
          orderComparisonSign o₁ σ e₁ hN₁ hSet₁ := by
    have hocc :
        orderComparisonSign o₁ σ (inducedFaceVertices o₁ hστ)
            (inducedFaceVertices_nodup o₁ hστ) (inducedFaceVertices_toFinset o₁ hστ) =
          orderComparisonSign o₁ σ e₁ hN₁ hSet₁ := by
      exact orderComparisonSign_congr (o := o₁) (σ := σ) hind₁
        (inducedFaceVertices_nodup o₁ hστ) hN₁
        (inducedFaceVertices_toFinset o₁ hστ) hSet₁
    simp [signedIncidence, hv, l₁, hocc]
  have hs₂ :
      signedIncidence o₂ hστ =
        Orientation.alternatingSign (l₂.idxOf v) *
          orderComparisonSign o₂ σ e₂ hN₂ hSet₂ := by
    have hocc :
        orderComparisonSign o₂ σ (inducedFaceVertices o₂ hστ)
            (inducedFaceVertices_nodup o₂ hστ) (inducedFaceVertices_toFinset o₂ hστ) =
          orderComparisonSign o₂ σ e₂ hN₂ hSet₂ := by
      exact orderComparisonSign_congr (o := o₂) (σ := σ) hind₂
        (inducedFaceVertices_nodup o₂ hστ) hN₂
        (inducedFaceVertices_toFinset o₂ hστ) hSet₂
    simp [signedIncidence, hv, l₂, hocc]
  rw [hs₁, hs₂, hσCompare, hEraseSign]
  calc
    Orientation.alternatingSign (l₁.idxOf v) *
        ((orientationSimplexSign o₁ o₂ τ *
            Orientation.alternatingSign (j₁ : ℕ) *
            Orientation.alternatingSign (j₂ : ℕ)) *
          orderComparisonSign o₂ σ e₂ hN₂ hSet₂ *
          orientationSimplexSign o₁ o₂ σ) =
      (Orientation.alternatingSign (l₁.idxOf v) *
          Orientation.alternatingSign (j₁ : ℕ)) *
        (orientationSimplexSign o₁ o₂ τ *
          orientationSimplexSign o₁ o₂ σ *
          (Orientation.alternatingSign (j₂ : ℕ) *
            orderComparisonSign o₂ σ e₂ hN₂ hSet₂)) := by
              ring
    _ =
      1 *
        (orientationSimplexSign o₁ o₂ τ *
          orientationSimplexSign o₁ o₂ σ *
          (Orientation.alternatingSign (j₂ : ℕ) *
            orderComparisonSign o₂ σ e₂ hN₂ hSet₂)) := by
              simp [j₁, alternatingSign_mul_self]
    _ =
      orientationSimplexSign o₁ o₂ τ *
        orientationSimplexSign o₁ o₂ σ *
        (Orientation.alternatingSign (l₂.idxOf v) *
          orderComparisonSign o₂ σ e₂ hN₂ hSet₂) := by
              simp [j₂]

theorem signedIncidence_eq_orientationSimplexSign_mul_of_qface
    (o₁ o₂ : Orientation K) {q : Nat}
    {σ : K.qSimplices q} {τ : K.qSimplices (q + 1)} (hστ : σ.1 ≤ τ.1) :
    signedIncidence o₁ hστ =
      orientationSimplexSign o₁ o₂ τ.1 *
        orientationSimplexSign o₁ o₂ σ.1 *
        signedIncidence o₂ hστ := by
  rcases deleted_toList_eq_singleton_of_qface (K := K) hστ with ⟨v, hv⟩
  simpa using signedIncidence_eq_orientationSimplexSign_mul
    (o₁ := o₁) (o₂ := o₂) (hστ := hστ) (v := v) hv

section SortedOrientation

variable [LinearOrder V]

/-- The standard orientation: vertices of each simplex sorted by the linear order. -/
noncomputable def sortedOrientation (K : SimplicialComplex V) : Orientation K where
  orderedVertices σ := σ.1.sort (· ≤ ·)
  nodup _ := Finset.sort_nodup _ _
  toFinset_eq _ := Finset.sort_toFinset _ _

/-- Filtering a sorted finset list by a subset gives the sorted list of the subset. -/
private theorem sort_filter_eq_sort {s t : Finset V} (hst : s ⊆ t) :
    (t.sort (· ≤ ·)).filter (· ∈ s) = s.sort (· ≤ ·) := by
  apply @List.eq_of_perm_of_sorted V (· ≤ ·)
  · rw [List.perm_ext_iff_of_nodup
      ((Finset.sort_nodup _ t).sublist List.filter_sublist)
      (Finset.sort_nodup _ s)]
    intro a
    simp only [List.mem_filter, Finset.mem_sort, decide_eq_true_eq]
    exact ⟨fun ⟨_, hs⟩ => hs, fun hs => ⟨hst hs, hs⟩⟩
  · exact (Finset.sort_sorted _ t).filter _
  · exact Finset.sort_sorted _ s

/-- For sorted orientation, induced face vertices equal the face's own ordered vertices. -/
theorem sortedOrientation_inducedFace_eq {K : SimplicialComplex V}
    {σ τ : K.Simplex} (hστ : σ ≤ τ) :
    inducedFaceVertices (sortedOrientation K) hστ =
      (sortedOrientation K).orderedVertices σ := by
  simp only [inducedFaceVertices, sortedOrientation]
  exact sort_filter_eq_sort hστ

/-- The sign of reorderPerm is 1 when the two lists are equal (as lists). -/
theorem sign_reorderPerm_eq_one_of_eq {l : List V}
    (h₁ h₂ : l.Nodup) (heq : l.toFinset = l.toFinset) :
    (Equiv.Perm.sign (reorderPerm h₁ h₂ heq) : ℤ) = 1 := by
  suffices reorderPerm h₁ h₂ heq = 1 by simp [this]
  ext i
  simp only [Equiv.Perm.one_apply]
  have hget := get_reorderPerm h₁ h₂ heq i
  -- hget : l.get(finCongr(...)(reorderPerm i)) = l.get i
  -- By nodup injectivity: finCongr(...)(reorderPerm i) = i
  have hinj := h₂.get_inj_iff.mp hget
  -- hinj : finCongr(...)(reorderPerm i) = i
  -- Goal : ↑(reorderPerm i) = ↑i  (these are Fin.val)
  -- finCongr preserves Fin.val, so (reorderPerm i).val = i.val
  have hval := congr_arg Fin.val hinj
  simp only [finCongr_apply] at hval
  exact hval

/-- orderComparisonSign is 1 when the comparison list equals orderedVertices. -/
theorem ocsign_eq_one_of_list_eq {o : Orientation K} {σ : K.Simplex}
    {l : List V} {hN : l.Nodup} {hSet : l.toFinset = σ.1}
    (heq : l = o.orderedVertices σ) :
    orderComparisonSign o σ l hN hSet = 1 := by
  subst heq
  simp only [orderComparisonSign]
  exact sign_reorderPerm_eq_one_of_eq _ _ _

/-- For sorted orientation, the orderComparisonSign is always 1. -/
theorem sortedOrientation_ocsign_eq_one {K : SimplicialComplex V}
    {σ τ : K.Simplex} (hστ : σ ≤ τ) :
    orderComparisonSign (sortedOrientation K) σ
      (inducedFaceVertices (sortedOrientation K) hστ)
      (inducedFaceVertices_nodup (sortedOrientation K) hστ)
      (inducedFaceVertices_toFinset (sortedOrientation K) hστ) = 1 :=
  ocsign_eq_one_of_list_eq (sortedOrientation_inducedFace_eq hστ)

/-- For sorted orientation, signedIncidence equals just alternatingSign of the deleted vertex
    position in the coface's sorted order. -/
theorem sortedOrientation_signedIncidence_mul_one {K : SimplicialComplex V}
    {σ τ : K.Simplex} (hστ : σ ≤ τ) {v : V}
    (hv : (τ.1 \ σ.1).toList = [v]) :
    signedIncidence (sortedOrientation K) hστ =
      alternatingSign ((τ.1.sort (· ≤ ·)).idxOf v) := by
  simp only [signedIncidence, sortedOrientation, hv]
  have h1 := sortedOrientation_ocsign_eq_one (V := V) (K := K) hστ
  simp only [orderComparisonSign, sortedOrientation] at h1 ⊢
  rw [h1, mul_one]

/-- Erasing an element from a sorted finset list gives the sorted list of the erasure. -/
theorem sort_erase_eq_erase_sort {s : Finset V} {a : V} (_ha : a ∈ s) :
    (s.erase a).sort (· ≤ ·) = (s.sort (· ≤ ·)).erase a := by
  have hes : ((s.sort (· ≤ ·)).erase a).Sublist (s.sort (· ≤ ·)) :=
    @List.erase_sublist _ _ (a := a) (l := s.sort (· ≤ ·))
  have hnodup_erase : ((s.sort (· ≤ ·)).erase a).Nodup :=
    (Finset.sort_nodup _ s).sublist hes
  apply @List.eq_of_perm_of_sorted V (· ≤ ·)
  · rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) hnodup_erase]
    intro b
    simp only [Finset.mem_sort, Finset.mem_erase]
    rw [(Finset.sort_nodup _ s).erase_eq_filter a]
    simp only [List.mem_filter, Finset.mem_sort, bne_iff_ne, ne_eq]
    tauto
  · exact Finset.sort_sorted _ _
  · exact (Finset.sort_sorted _ s).sublist hes

end SortedOrientation

end Orientation

end PersistentSheafLaplacian
end HeytingLean
