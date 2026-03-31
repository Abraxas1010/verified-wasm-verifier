import HeytingLean.InqBQ.Finiteness
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.SuccPred

namespace HeytingLean
namespace InqBQ

open Set
open SigmaAB

variable {M : InfoModel SigmaAB}

/-- Top is supported at every state. -/
theorem supports_top (M : InfoModel SigmaAB) (s : Set M.W) (g : Assignment M.D) :
    supports M s g Formula.top := by
  intro t ht hBot
  exact hBot

/-- Conjoin `x_k ≠ x_i` for all `i < m`. -/
def allNeqTo (k : Nat) : Nat → Formula SigmaAB
  | 0 => Formula.top
  | m + 1 => .conj (neq (.var m) (.var k)) (allNeqTo k m)

/-- Pairwise disequality among the first `n` variables. -/
def chiCore : Nat → Formula SigmaAB
  | 0 => Formula.top
  | n + 1 => .conj (chiCore n) (allNeqTo n n)

/-- Bind the first `n` variables using inquisitive existential quantification. -/
def bindExists : Nat → Formula SigmaAB → Formula SigmaAB
  | 0, φ => φ
  | n + 1, φ => .inqExists n (bindExists n φ)

/-- `χₙ` says that there are at least `n` distinct objects. -/
def chiN (n : Nat) : Formula SigmaAB :=
  bindExists n (chiCore n)

/-- Crude syntactic size used to bound the `χₙ` witnesses in finite subsets. -/
def formulaSize : Formula SigmaAB → Nat
  | .pred _ _ => 1
  | .eq _ _ => 1
  | .bot => 1
  | .conj φ ψ => formulaSize φ + formulaSize ψ + 1
  | .inqDisj φ ψ => formulaSize φ + formulaSize ψ + 1
  | .imp φ ψ => formulaSize φ + formulaSize ψ + 1
  | .forall_ _ φ => formulaSize φ + 1
  | .inqExists _ φ => formulaSize φ + 1

theorem chiCore_size_lower : ∀ n, n ≤ formulaSize (chiCore n)
  | 0 => by simp [chiCore, Formula.top, Formula.neg, formulaSize]
  | n + 1 => by
      calc
        n + 1 ≤ formulaSize (chiCore n) + 1 := Nat.succ_le_succ (chiCore_size_lower n)
        _ ≤ formulaSize (chiCore n) + formulaSize (allNeqTo n n) + 1 := by omega
        _ = formulaSize (chiCore (n + 1)) := by
              simp [chiCore, formulaSize, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem formulaSize_bindExists : ∀ n φ, formulaSize (bindExists n φ) = formulaSize φ + n
  | 0, φ => by simp [bindExists, formulaSize]
  | n + 1, φ => by
      simp [bindExists, formulaSize, formulaSize_bindExists n φ, Nat.add_assoc, Nat.add_left_comm]

theorem chiN_size_lower : ∀ n, n ≤ formulaSize (chiN n)
  | n => by
      rw [chiN, formulaSize_bindExists]
      exact Nat.le_add_left _ _

/-- Overwrite the first `n` variables with a tuple of values. -/
def tupleAssign (g : Assignment M.D) {n : Nat} (xs : Fin n → M.D) : Assignment M.D :=
  fun k => if h : k < n then xs ⟨k, h⟩ else g k

@[simp] theorem tupleAssign_lt (g : Assignment M.D) {n : Nat} (xs : Fin n → M.D)
    {k : Nat} (hk : k < n) :
    tupleAssign g xs k = xs ⟨k, hk⟩ := by
  simp [tupleAssign, hk]

@[simp] theorem tupleAssign_ge (g : Assignment M.D) {n : Nat} (xs : Fin n → M.D)
    {k : Nat} (hk : n ≤ k) :
    tupleAssign g xs k = g k := by
  have hnk : ¬ k < n := by omega
  simp [tupleAssign, hnk]

def snocTuple {n : Nat} (xs : Fin n → M.D) (d : M.D) : Fin (n + 1) → M.D :=
  fun i =>
    if h : (i : Nat) < n then
      xs ⟨i, h⟩
    else
      d

@[simp] theorem snocTuple_castSucc {n : Nat} (xs : Fin n → M.D) (d : M.D) (i : Fin n) :
    snocTuple xs d i.castSucc = xs i := by
  simp [snocTuple, i.is_lt]

@[simp] theorem snocTuple_last {n : Nat} (xs : Fin n → M.D) (d : M.D) :
    snocTuple xs d (Fin.last n) = d := by
  simp [snocTuple]

@[simp] theorem snocTuple_castSucc_last {n : Nat} (xs : Fin (n + 1) → M.D) :
    snocTuple (fun i : Fin n => xs i.castSucc) (xs (Fin.last n)) = xs := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp
  · simp

theorem tupleAssign_update_eq {n : Nat} (g : Assignment M.D) (xs : Fin n → M.D) (d : M.D) :
    tupleAssign (Assignment.update g n d) xs = tupleAssign g (snocTuple xs d) := by
  funext k
  by_cases hk : k < n
  · have hkn : k ≠ n := by omega
    have hk1 : k < n + 1 := by omega
    simp [tupleAssign, hk, hk1, snocTuple, Assignment.update, hkn]
  · by_cases hkn : k = n
    · subst hkn
      simp [tupleAssign, hk, snocTuple, Assignment.update]
    · have hkge : n + 1 ≤ k := by omega
      have hknot : ¬ k < n + 1 := by omega
      simp [tupleAssign, hk, hknot, Assignment.update, hkn]

theorem tupleAssign_zero (g : Assignment M.D) :
    tupleAssign g (n := 0) (fun i => Fin.elim0 i) = g := by
  funext k
  simp [tupleAssign]

theorem supports_bindExists_iff (M : InfoModel SigmaAB) (s : Set M.W)
    (g : Assignment M.D) (φ : Formula SigmaAB) :
    ∀ n, supports M s g (bindExists n φ) ↔
      ∃ xs : Fin n → M.D, supports M s (tupleAssign g xs) φ
  | 0 => by
      constructor
      · intro h
        refine ⟨fun i => Fin.elim0 i, ?_⟩
        simpa [bindExists, tupleAssign_zero] using h
      · rintro ⟨xs, h⟩
        simpa [bindExists, tupleAssign_zero] using h
  | n + 1 => by
      constructor
      · rintro ⟨d, hd⟩
        rcases (supports_bindExists_iff M s (Assignment.update g n d) φ n).1 hd with ⟨xs, hxs⟩
        refine ⟨snocTuple xs d, ?_⟩
        simpa [bindExists, tupleAssign_update_eq] using hxs
      · rintro ⟨xs, hxs⟩
        refine ⟨xs (Fin.last n), ?_⟩
        have hEq :
            tupleAssign (Assignment.update g n (xs (Fin.last n))) (fun i : Fin n => xs i.castSucc) =
              tupleAssign g xs := by
          calc
            tupleAssign (Assignment.update g n (xs (Fin.last n))) (fun i : Fin n => xs i.castSucc)
                = tupleAssign g (snocTuple (fun i : Fin n => xs i.castSucc) (xs (Fin.last n))) := by
                    simpa using tupleAssign_update_eq (g := g)
                      (xs := fun i : Fin n => xs i.castSucc) (d := xs (Fin.last n))
            _ = tupleAssign g xs := by
                  simp [snocTuple_castSucc_last]
        exact (supports_bindExists_iff M s (Assignment.update g n (xs (Fin.last n))) φ n).2
          ⟨fun i : Fin n => xs i.castSucc, by simpa [hEq] using hxs⟩

theorem globallySupports_neq_vars_iff
    (hid : M.isIdModel) (g : Assignment M.D) (i j : Nat) :
    globallySupports M g (neq (.var i) (.var j)) ↔ g i ≠ g j := by
  constructor
  · intro hneq hEq
    rcases M.hW with ⟨w⟩
    have hEqSupp : supports M ({w} : Set M.W) g (.eq (.var i) (.var j)) := by
      intro w' hw'
      have hw' : w' = w := by simpa using hw'
      simpa [denote, hw', hEq] using (hid w (g i) (g j)).2 hEq
    have hBot := hneq ({w} : Set M.W) (by
      intro u hu
      simp at hu
      subst hu
      simp) hEqSupp
    have hwMem : w ∈ ({w} : Set M.W) := by simp
    have hEmpty : ({w} : Set M.W) = ∅ := hBot
    simpa [hEmpty] using hwMem
  · intro hneq
    intro t ht hEq
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hLoc : M.localEq w (g i) (g j) := by
      simpa [denote] using hEq w hw
    exact hneq ((hid w (g i) (g j)).1 hLoc)

theorem globallySupports_allNeqTo_iff
    (hid : M.isIdModel) (g : Assignment M.D) (k : Nat) :
    ∀ m, globallySupports M g (allNeqTo k m) ↔
      ∀ i : Fin m, g i ≠ g k
  | 0 => by
      constructor
      · intro _
        intro i
        exact Fin.elim0 i
      · intro _
        exact supports_top M Set.univ g
  | m + 1 => by
      constructor
      · rintro ⟨hHead, hTail⟩
        intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · exact (globallySupports_allNeqTo_iff hid g k m).1 hTail j
        · exact (globallySupports_neq_vars_iff hid g m k).1 hHead
      · intro h
        refine ⟨?_, ?_⟩
        · exact (globallySupports_neq_vars_iff hid g m k).2 (h (Fin.last m))
        · apply (globallySupports_allNeqTo_iff hid g k m).2
          intro i
          exact h i.castSucc

theorem globallySupports_chiCore_iff
    (hid : M.isIdModel) (g : Assignment M.D) :
    ∀ n, globallySupports M g (chiCore n) ↔ Function.Injective (fun i : Fin n => g i)
  | 0 => by
      constructor
      · intro _
        intro i
        exact Fin.elim0 i
      · intro _
        exact supports_top M Set.univ g
  | n + 1 => by
      constructor
      · rintro ⟨hCore, hNew⟩
        have hInj : Function.Injective (fun i : Fin n => g i) :=
          (globallySupports_chiCore_iff hid g n).1 hCore
        have hNeq : ∀ i : Fin n, g i ≠ g n :=
          (globallySupports_allNeqTo_iff hid g n n).1 hNew
        intro i j hij
        rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
        · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
          · exact congrArg Fin.castSucc (hInj hij)
          · exfalso
            exact hNeq i' (by simpa using hij)
        · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
          · exfalso
            exact hNeq j' (show g j' = g n by simpa using hij.symm)
          · rfl
      · intro hInj
        refine ⟨?_, ?_⟩
        · apply (globallySupports_chiCore_iff hid g n).2
          intro i j hij
          exact Fin.castSucc_injective _ (hInj (by simpa using hij))
        · apply (globallySupports_allNeqTo_iff hid g n n).2
          intro i
          intro hEq
          have : i.castSucc = Fin.last n := hInj <| by simpa using hEq
          exact i.castSucc_ne_last this

theorem globallySupports_chiN_iff_embedding
    (hid : M.isIdModel) (g : Assignment M.D) (n : Nat) :
    globallySupports M g (chiN n) ↔ Nonempty (Fin n ↪ M.D) := by
  change supports M Set.univ g (bindExists n (chiCore n)) ↔ Nonempty (Fin n ↪ M.D)
  rw [supports_bindExists_iff (M := M) (s := Set.univ) (g := g) (φ := chiCore n) n]
  constructor
  · rintro ⟨xs, hxs⟩
    refine ⟨{ toFun := xs, inj' := ?_ }⟩
    intro i j hij
    have hTupleInj : Function.Injective (fun i : Fin n => tupleAssign g xs i) :=
      (globallySupports_chiCore_iff hid (tupleAssign g xs) n).1 hxs
    exact hTupleInj (by simpa [tupleAssign] using hij)
  · rintro ⟨e⟩
    refine ⟨e, ?_⟩
    apply (globallySupports_chiCore_iff hid (tupleAssign g e) n).2
    intro i j hij
    apply e.injective
    simpa [tupleAssign] using hij

theorem models_chiN_iff_card_ge
    (hid : M.isIdModel) (g : Assignment M.D) (n : Nat) :
    globallySupports M g (chiN n) ↔ ∃ s : Finset M.D, s.card ≥ n := by
  constructor
  · rintro h
    rcases (globallySupports_chiN_iff_embedding hid g n).1 h with ⟨e⟩
    refine ⟨Finset.univ.map e, ?_⟩
    simpa [Fintype.card_fin] using
      le_of_eq (Finset.card_map e (Finset.univ : Finset (Fin n)))
  · rintro ⟨s, hs⟩
    have hs' : n ≤ s.card := hs
    let e0 : Fin s.card ↪ M.D :=
      (s.equivFin.symm.toEmbedding).trans
        ⟨Subtype.val, fun _ _ h => Subtype.ext h⟩
    let e : Fin n ↪ M.D := (Fin.castLEEmb hs').trans e0
    exact (globallySupports_chiN_iff_embedding hid g n).2 ⟨e⟩

/-- Restrict a `SigmaAB`-model to a nonempty information state. -/
def restrictedModel (M : InfoModel SigmaAB) (s : Set M.W) (hs : s.Nonempty) : InfoModel SigmaAB where
  W := s
  D := M.D
  hW := by
    rcases hs with ⟨w, hw⟩
    exact ⟨⟨w, hw⟩⟩
  hD := M.hD
  predInterp := fun w P => PEmpty.elim P
  rigidInterp := fun f => PEmpty.elim f
  nonrigidInterp := fun w f args => M.nonrigidInterp w.1 f args
  localEq := fun w => M.localEq w.1
  localEq_equiv := by
    intro w
    exact M.localEq_equiv w.1
  localEq_congr_pred := by
    intro w P
    exact PEmpty.elim P
  localEq_congr_rigid := by
    intro w f
    exact PEmpty.elim f
  localEq_congr_nonrigid := by
    intro w f xs ys hxy
    exact M.localEq_congr_nonrigid hxy

@[simp] theorem denote_restricted
    (s : Set M.W) (hs : s.Nonempty) (w : (restrictedModel M s hs).W) (g : Assignment M.D)
    (t : Term SigmaAB) :
    denote (restrictedModel M s hs) w g t = denote M w.1 g t := by
  induction t with
  | var x => rfl
  | rigidApp f args ih => cases f
  | nonrigidApp f args ih =>
      simp [denote]
      congr
      funext i
      exact ih i

theorem restricted_val_image (s : Set M.W) (hs : s.Nonempty) :
    Subtype.val '' (Set.univ : Set (restrictedModel M s hs).W) = s := by
  ext w
  constructor
  · rintro ⟨w', -, rfl⟩
    exact w'.2
  · intro hw
    exact ⟨⟨w, hw⟩, by simp, rfl⟩

def liftToRestricted (s : Set M.W) (hs : s.Nonempty) (u : Set M.W) :
    Set (restrictedModel M s hs).W :=
  { w | w.1 ∈ u }

theorem image_liftToRestricted
    (s : Set M.W) (hs : s.Nonempty) {u : Set M.W} (hu : u ⊆ s) :
    Subtype.val '' liftToRestricted (M := M) s hs u = u := by
  ext w
  constructor
  · rintro ⟨w', hw', rfl⟩
    exact hw'
  · intro hw
    exact ⟨⟨w, hu hw⟩, hw, rfl⟩

theorem liftToRestricted_image
    (s : Set M.W) (hs : s.Nonempty) (t : Set (restrictedModel M s hs).W) :
    liftToRestricted (M := M) s hs (Subtype.val '' t) = t := by
  ext w
  constructor
  · intro hw
    rcases hw with ⟨w', hw', hwEq⟩
    have : w' = w := Subtype.ext hwEq
    simpa [this] using hw'
  · intro hw
    exact ⟨w, hw, rfl⟩

theorem supports_restricted_iff
    (s : Set M.W) (hs : s.Nonempty) (t : Set (restrictedModel M s hs).W)
    (g : Assignment M.D) :
    ∀ φ : Formula SigmaAB,
      supports (restrictedModel M s hs) t g φ ↔ supports M (Subtype.val '' t) g φ
  | .pred P args => by cases P
  | .eq u v => by
      constructor
      · intro h w hw
        rcases hw with ⟨w', hw', rfl⟩
        simpa [denote_restricted] using h w' hw'
      · intro h w hw
        simpa [denote_restricted] using h w.1 ⟨w, hw, rfl⟩
  | .bot => by
      constructor
      · intro ht
        subst ht
        simpa [supports]
      · intro hImg
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro w hw
        have hEmpty : Subtype.val '' t = ∅ := hImg
        have : w.1 ∈ (∅ : Set M.W) := by
          rw [← hEmpty]
          exact ⟨w, hw, rfl⟩
        simpa using this
  | .conj φ ψ => by
      simp [supports, supports_restricted_iff s hs t g φ, supports_restricted_iff s hs t g ψ]
  | .inqDisj φ ψ => by
      simp [supports, supports_restricted_iff s hs t g φ, supports_restricted_iff s hs t g ψ]
  | .imp φ ψ => by
      constructor
      · intro h u hu hφ
        have hu_s : u ⊆ s := by
          intro w hw
          rcases hu hw with ⟨w', hw', hwEq⟩
          simpa [hwEq] using w'.2
        let u' := liftToRestricted (M := M) s hs u
        have hu' : u' ⊆ t := by
          intro w hw
          rcases hu hw with ⟨w', hw', hwEq⟩
          have : w' = w := Subtype.ext hwEq
          simpa [u', this] using hw'
        have hφ' : supports (restrictedModel M s hs) u' g φ := by
          apply (supports_restricted_iff s hs u' g φ).2
          simpa [u', image_liftToRestricted (M := M) s hs hu_s] using hφ
        have hψ' : supports (restrictedModel M s hs) u' g ψ := h u' hu' hφ'
        have hψ'' := (supports_restricted_iff s hs u' g ψ).1 hψ'
        simpa [u', image_liftToRestricted (M := M) s hs hu_s] using hψ''
      · intro h u hu hφ
        let u' : Set M.W := Subtype.val '' u
        have hu' : u' ⊆ Subtype.val '' t := by
          intro w hw
          rcases hw with ⟨w', hw', rfl⟩
          exact ⟨w', hu hw', rfl⟩
        have hφ' : supports M u' g φ := (supports_restricted_iff s hs u g φ).1 hφ
        have hψ' : supports M u' g ψ := h u' hu' hφ'
        have hu's : u' ⊆ s := by
          intro w hw
          rcases hw with ⟨w', -, rfl⟩
          exact w'.2
        have hψ'' : supports (restrictedModel M s hs) (liftToRestricted (M := M) s hs u') g ψ := by
          apply (supports_restricted_iff s hs (liftToRestricted (M := M) s hs u') g ψ).2
          simpa [image_liftToRestricted (M := M) s hs hu's] using hψ'
        simpa [u', liftToRestricted_image (M := M) s hs u] using hψ''
  | .forall_ x φ => by
      constructor
      · intro h d
        exact (supports_restricted_iff s hs t (Assignment.update g x d) φ).1 (h d)
      · intro h d
        exact (supports_restricted_iff s hs t (Assignment.update g x d) φ).2 (h d)
  | .inqExists x φ => by
      constructor
      · rintro ⟨d, hd⟩
        exact ⟨d, (supports_restricted_iff s hs t (Assignment.update g x d) φ).1 hd⟩
      · rintro ⟨d, hd⟩
        exact ⟨d, (supports_restricted_iff s hs t (Assignment.update g x d) φ).2 hd⟩

theorem globallySupports_restricted_iff
    (s : Set M.W) (hs : s.Nonempty) (g : Assignment M.D) (φ : Formula SigmaAB) :
    globallySupports (restrictedModel M s hs) g φ ↔ supports M s g φ := by
  simpa [globallySupports, restricted_val_image (M := M) s hs] using
    (supports_restricted_iff (M := M) s hs Set.univ g φ)

theorem restrictedModel_isIdModel
    (s : Set M.W) (hs : s.Nonempty) (hid : M.isIdModel) :
    (restrictedModel M s hs).isIdModel := by
  intro w d e
  exact hid w.1 d e

/-- The non-compactness witness set: finiteness together with arbitrarily large finite lower bounds. -/
def GammaNC : Set (Formula SigmaAB) :=
  {eta} ∪ Set.range chiN

theorem gammaNC_idEntails_theta : idEntails GammaNC theta := by
  intro M hid s g hΓ
  by_cases hs : s = ∅
  · subst hs
    exact supports_empty M g theta
  · let hsne : s.Nonempty := Set.nonempty_iff_ne_empty.mpr hs
    let N := restrictedModel M s hsne
    have hidN : N.isIdModel := restrictedModel_isIdModel (M := M) s hsne hid
    have hEtaN : globallySupports N g eta := by
      simpa [N] using
        (globallySupports_restricted_iff (M := M) s hsne g eta).2
          (hΓ eta (by
            left
            simp))
    have hChiN (n : Nat) : globallySupports N g (chiN n) := by
      simpa [N] using
        (globallySupports_restricted_iff (M := M) s hsne g (chiN n)).2
          (hΓ (chiN n) (by
            right
            exact ⟨n, rfl⟩))
    by_contra hNotTheta
    have hNotThetaN : ¬ globallySupports N g theta := by
      intro hThetaN
      exact hNotTheta <|
        (globallySupports_restricted_iff (M := M) s hsne g theta).1 (by
          simpa [N] using hThetaN)
    have hFullN : isFull N := by
      by_contra hNotFull
      exact hNotThetaN ((theta_captures_nonfullness (M := N) hidN g).2 hNotFull)
    have hFinite : Finite N.D :=
      (eta_captures_finiteness (M := N) hFullN hidN g).1 hEtaN
    letI : Fintype N.D := Fintype.ofFinite N.D
    rcases (models_chiN_iff_card_ge (M := N) hidN g (Fintype.card N.D + 1)).1
        (hChiN (Fintype.card N.D + 1)) with ⟨u, hu⟩
    have hLe : u.card ≤ Fintype.card N.D := u.card_le_univ
    omega

theorem canonicalFull_supports_chiN
    (m n : Nat) (g : Assignment (Fin (m + 1))) (h : n ≤ m + 1) :
    globallySupports (canonicalFull (Fin (m + 1))) g (chiN n) := by
  apply (globallySupports_chiN_iff_embedding
    (M := canonicalFull (Fin (m + 1)))
    (canonicalFull_isIdModel (Fin (m + 1))) g n).2
  exact ⟨Fin.castLEEmb h⟩

theorem canonicalFull_not_theta
    (m : Nat) (g : Assignment (Fin (m + 1))) :
    ¬ globallySupports (canonicalFull (Fin (m + 1))) g theta := by
  intro hTheta
  have hNotFull :
      ¬ isFull (canonicalFull (Fin (m + 1))) :=
    (theta_captures_nonfullness
      (M := canonicalFull (Fin (m + 1)))
      (canonicalFull_isIdModel (Fin (m + 1))) g).1 hTheta
  exact hNotFull (canonicalFull_isFull (Fin (m + 1)))

theorem finite_gammaNC_countermodel
    (Γ0 : Finset (Formula SigmaAB))
    (hsub : ∀ φ, φ ∈ Γ0 → φ ∈ GammaNC) :
    let m := Γ0.sum formulaSize
    let g : Assignment (Fin (m + 1)) := fun _ => ⟨0, Nat.succ_pos _⟩
    (∀ φ, φ ∈ Γ0 → globallySupports (canonicalFull (Fin (m + 1))) g φ) ∧
      ¬ globallySupports (canonicalFull (Fin (m + 1))) g theta := by
  classical
  dsimp
  refine ⟨?_, canonicalFull_not_theta _ _⟩
  intro φ hφ
  have hmem := hsub φ hφ
  rcases hmem with hEta | ⟨n, rfl⟩
  · subst hEta
    exact
      (eta_captures_finiteness
        (M := canonicalFull (Fin (Γ0.sum formulaSize + 1)))
        (canonicalFull_isFull (Fin (Γ0.sum formulaSize + 1)))
        (canonicalFull_isIdModel (Fin (Γ0.sum formulaSize + 1)))
        (fun _ => ⟨0, Nat.succ_pos _⟩)).2
        (show Finite (Fin (Γ0.sum formulaSize + 1)) from inferInstance)
  · have hLeSize : formulaSize (chiN n) ≤ Γ0.sum formulaSize := by
      have hsum :
          Γ0.sum formulaSize =
            formulaSize (chiN n) + (Γ0.erase (chiN n)).sum formulaSize := by
        rw [← Finset.insert_erase (s := Γ0) (a := chiN n) (by simpa using hφ)]
        rw [Finset.sum_insert]
        · simp
        · simp
      rw [hsum]
      exact Nat.le_add_right _ _
    exact canonicalFull_supports_chiN (Γ0.sum formulaSize) n (fun _ => ⟨0, Nat.succ_pos _⟩)
      (le_trans (chiN_size_lower n) (Nat.le_succ_of_le hLeSize))

theorem no_finite_subset_idEntails_theta :
    ¬ ∃ Γ0 : Finset (Formula SigmaAB),
      (∀ φ, φ ∈ Γ0 → φ ∈ GammaNC) ∧ idEntails (↑Γ0 : Set (Formula SigmaAB)) theta := by
  classical
  intro h
  rcases h with ⟨Γ0, hsub, hEnt⟩
  let m := Γ0.sum formulaSize
  let g : Assignment (Fin (m + 1)) := fun _ => ⟨0, Nat.succ_pos _⟩
  have hCounter := finite_gammaNC_countermodel Γ0 hsub
  rcases hCounter with ⟨hAll, hNotTheta⟩
  exact hNotTheta <|
    hEnt (canonicalFull (Fin (m + 1))) (canonicalFull_isIdModel (Fin (m + 1))) Set.univ g
      (by
        intro φ hφ
        exact hAll φ hφ)

theorem inqbq_not_compact_id :
    ∃ Γ : Set (Formula SigmaAB), ∃ ψ : Formula SigmaAB,
      idEntails Γ ψ ∧
      ¬ ∃ Γ0 : Finset (Formula SigmaAB),
        (∀ φ, φ ∈ Γ0 → φ ∈ Γ) ∧ idEntails (↑Γ0 : Set (Formula SigmaAB)) ψ := by
  refine ⟨GammaNC, theta, gammaNC_idEntails_theta, ?_⟩
  exact no_finite_subset_idEntails_theta

theorem supports_rhoRigidEq_assignment_irrel
    (M : InfoModel SigmaAB) (s : Set M.W) (g g' : Assignment M.D) :
    supports M s g rhoRigidEq ↔ supports M s g' rhoRigidEq := by
  constructor <;> intro h <;> intro d e <;>
    simpa [rhoRigidEq, Formula.question, denote, Assignment.update] using h d e

theorem rhoRigidEq_localEq_iff
    {s : Set M.W} {w0 w : M.W} (hw0 : w0 ∈ s) (hw : w ∈ s)
    {g : Assignment M.D} (hRho : supports M s g rhoRigidEq) (d e : M.D) :
    M.localEq w d e ↔ M.localEq w0 d e := by
  have hQuest :
      supports M s ((Assignment.update g 0 d).update 1 e)
        (Formula.question (.eq (.var 0) (.var 1))) := by
    simpa [rhoRigidEq] using hRho d e
  rcases hQuest with hEq | hNeg
  · constructor
    · intro _
      exact hEq w0 hw0
    · intro _
      exact hEq w hw
  · have hNoLocal : ∀ ⦃u : M.W⦄, u ∈ s → ¬ M.localEq u d e := by
      intro u hu hLoc
      have hEqSingleton :
          supports M ({u} : Set M.W) ((Assignment.update g 0 d).update 1 e)
            (.eq (.var 0) (.var 1)) := by
        intro u' hu'
        have hu' : u' = u := by simpa using hu'
        subst hu'
        simpa [denote]
      have hBot : ({u} : Set M.W) = ∅ :=
        hNeg ({u} : Set M.W) (by
          intro x hx
          have hx' : x = u := by simpa using hx
          subst hx'
          exact hu) hEqSingleton
      have : u ∈ (∅ : Set M.W) := by
        have huSingleton : u ∈ ({u} : Set M.W) := by simp
        simpa [hBot] using huSingleton
      simpa using this
    constructor
    · intro hLoc
      exact False.elim <| hNoLocal hw hLoc
    · intro hLoc
      exact False.elim <| hNoLocal hw0 hLoc

/-- Quotient the domain by the state-stable equality relation extracted from `rhoRigidEq`. -/
def rhoSetoid (M : InfoModel SigmaAB) (w0 : M.W) : Setoid M.D where
  r := M.localEq w0
  iseqv := M.localEq_equiv w0

abbrev RhoQuot (M : InfoModel SigmaAB) (w0 : M.W) :=
  Quotient (rhoSetoid M w0)

def liftAssign (M : InfoModel SigmaAB) (w0 : M.W) (g : Assignment M.D) :
    Assignment (RhoQuot M w0) :=
  fun n => Quotient.mk (rhoSetoid M w0) (g n)

@[simp] theorem liftAssign_update
    (M : InfoModel SigmaAB) (w0 : M.W) (g : Assignment M.D) (x : ℕ) (d : M.D) :
    liftAssign M w0 (Assignment.update g x d) =
      Assignment.update (liftAssign M w0 g) x (Quotient.mk (rhoSetoid M w0) d) := by
  funext y
  by_cases hy : y = x
  · subst hy
    simp [liftAssign, Assignment.update]
  · simp [liftAssign, Assignment.update, hy]

/-- State-local id-model induced by quotienting through `rhoRigidEq`. -/
def rhoQuotModel (M : InfoModel SigmaAB) (w0 : M.W) : InfoModel SigmaAB where
  W := M.W
  D := RhoQuot M w0
  hW := M.hW
  hD := ⟨Quotient.mk (rhoSetoid M w0) (Classical.choice M.hD)⟩
  predInterp := fun _ P => PEmpty.elim P
  rigidInterp := fun f => PEmpty.elim f
  nonrigidInterp := fun w f _ =>
    Quotient.mk (rhoSetoid M w0) (M.nonrigidInterp w f noArgs)
  localEq := fun _ x y => x = y
  localEq_equiv := by
    intro w
    exact ⟨fun x => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
  localEq_congr_pred := by
    intro w P
    exact PEmpty.elim P
  localEq_congr_rigid := by
    intro w f
    exact PEmpty.elim f
  localEq_congr_nonrigid := by
    intro w f xs ys hxy
    cases f <;> rfl

theorem rhoQuotModel_isIdModel (M : InfoModel SigmaAB) (w0 : M.W) :
    (rhoQuotModel M w0).isIdModel := by
  intro w d e
  rfl

@[simp] theorem denote_rhoQuotModel
    (M : InfoModel SigmaAB) (w0 w : M.W) (g : Assignment M.D) :
    ∀ t : Term SigmaAB,
      denote (rhoQuotModel M w0) w (liftAssign M w0 g) t =
        Quotient.mk (rhoSetoid M w0) (denote M w g t)
  | .var x => rfl
  | .rigidApp f args => PEmpty.elim f
  | .nonrigidApp f args => by
      have hArgs : args = noArgs := by
        funext i
        exact Fin.elim0 i
      subst hArgs
      have hNoArgs : (fun i => denote M w g (noArgs i)) = noArgs := by
        funext i
        exact Fin.elim0 i
      have hNoArgsQ :
          (fun i => denote (rhoQuotModel M w0) w (liftAssign M w0 g) (noArgs i)) = noArgs := by
        funext i
        exact Fin.elim0 i
      cases f
      · exact Quotient.sound <| by
          change M.localEq w0
            (M.nonrigidInterp w ABConst.a noArgs)
            (M.nonrigidInterp w ABConst.a (fun i => denote M w g (noArgs i)))
          have hInterp :
              M.nonrigidInterp w ABConst.a noArgs =
                M.nonrigidInterp w ABConst.a (fun i => denote M w g (noArgs i)) := by
            simpa using congrArg (M.nonrigidInterp w ABConst.a) hNoArgs.symm
          exact hInterp ▸ (M.localEq_equiv w0).1 (M.nonrigidInterp w ABConst.a noArgs)
      · exact Quotient.sound <| by
          change M.localEq w0
            (M.nonrigidInterp w ABConst.b noArgs)
            (M.nonrigidInterp w ABConst.b (fun i => denote M w g (noArgs i)))
          have hInterp :
              M.nonrigidInterp w ABConst.b noArgs =
                M.nonrigidInterp w ABConst.b (fun i => denote M w g (noArgs i)) := by
            simpa using congrArg (M.nonrigidInterp w ABConst.b) hNoArgs.symm
          exact hInterp ▸ (M.localEq_equiv w0).1 (M.nonrigidInterp w ABConst.b noArgs)

theorem supports_rhoQuotModel_iff
    {s : Set M.W} {w0 : M.W} (hw0 : w0 ∈ s)
    {gρ : Assignment M.D} (hRho : supports M s gρ rhoRigidEq) :
    ∀ {t : Set M.W} {g : Assignment M.D} (ht : t ⊆ s) (φ : Formula SigmaAB),
      supports M t g φ ↔
        supports (rhoQuotModel M w0) t (liftAssign M w0 g) φ
  | t, g, ht, .pred P args => PEmpty.elim P
  | t, g, ht, .eq u v => by
      constructor
      · intro hEq w hw
        have hLoc : M.localEq w (denote M w g u) (denote M w g v) := hEq w hw
        have hEqQ :
            denote (rhoQuotModel M w0) w (liftAssign M w0 g) u =
              denote (rhoQuotModel M w0) w (liftAssign M w0 g) v := by
          simpa only [denote_rhoQuotModel] using
            (Quotient.sound <| (rhoRigidEq_localEq_iff hw0 (ht hw)
              ((supports_rhoRigidEq_assignment_irrel M s gρ g).1 hRho)
              (denote M w g u) (denote M w g v)).1 hLoc)
        simpa [rhoQuotModel] using hEqQ
      · intro hEq w hw
        have hEqQ :
            Quotient.mk (rhoSetoid M w0) (denote M w g u) =
              Quotient.mk (rhoSetoid M w0) (denote M w g v) := by
          simpa only [denote_rhoQuotModel] using hEq w hw
        have hBase :
            M.localEq w0 (denote M w g u) (denote M w g v) := by
          exact Quotient.exact hEqQ
        exact (rhoRigidEq_localEq_iff hw0 (ht hw)
          ((supports_rhoRigidEq_assignment_irrel M s gρ g).1 hRho)
          (denote M w g u) (denote M w g v)).2 hBase
  | t, g, ht, .bot => by
      constructor
      · intro hBot
        exact hBot
      · intro hBot
        exact hBot
  | t, g, ht, .conj φ ψ => by
      constructor
      · rintro ⟨hφ, hψ⟩
        exact ⟨(supports_rhoQuotModel_iff hw0 hRho ht φ).1 hφ,
          (supports_rhoQuotModel_iff hw0 hRho ht ψ).1 hψ⟩
      · rintro ⟨hφ, hψ⟩
        exact ⟨(supports_rhoQuotModel_iff hw0 hRho ht φ).2 hφ,
          (supports_rhoQuotModel_iff hw0 hRho ht ψ).2 hψ⟩
  | t, g, ht, .inqDisj φ ψ => by
      constructor
      · intro h
        rcases h with hφ | hψ
        · exact Or.inl ((supports_rhoQuotModel_iff hw0 hRho ht φ).1 hφ)
        · exact Or.inr ((supports_rhoQuotModel_iff hw0 hRho ht ψ).1 hψ)
      · intro h
        rcases h with hφ | hψ
        · exact Or.inl ((supports_rhoQuotModel_iff hw0 hRho ht φ).2 hφ)
        · exact Or.inr ((supports_rhoQuotModel_iff hw0 hRho ht ψ).2 hψ)
  | t, g, ht, .imp φ ψ => by
      constructor
      · intro hImp u hu hφ
        have hu' : u ⊆ s := Subset.trans hu ht
        have hφ' :
            supports M u g φ :=
          (supports_rhoQuotModel_iff hw0 hRho hu' φ).2 hφ
        have hψ' : supports M u g ψ := hImp u hu hφ'
        exact (supports_rhoQuotModel_iff hw0 hRho hu' ψ).1 hψ'
      · intro hImp u hu hφ
        have hu' : u ⊆ s := Subset.trans hu ht
        have hφ' :
            supports (rhoQuotModel M w0) u (liftAssign M w0 g) φ :=
          (supports_rhoQuotModel_iff hw0 hRho hu' φ).1 hφ
        have hψ' : supports (rhoQuotModel M w0) u (liftAssign M w0 g) ψ :=
          hImp u hu hφ'
        exact (supports_rhoQuotModel_iff hw0 hRho hu' ψ).2 hψ'
  | t, g, ht, .forall_ x φ => by
      constructor
      · intro h qd
        let d : M.D := Quotient.out qd
        have hqd : Quotient.mk (rhoSetoid M w0) d = qd := Quotient.out_eq qd
        have hφ :
            supports (rhoQuotModel M w0) t
              (liftAssign M w0 (Assignment.update g x d)) φ :=
          (supports_rhoQuotModel_iff hw0 hRho ht φ).1 (h d)
        simpa [liftAssign_update, d, hqd] using hφ
      · intro h d
        have hφ :
            supports (rhoQuotModel M w0) t
              (liftAssign M w0 (Assignment.update g x d)) φ := by
          simpa [liftAssign_update] using h (Quotient.mk (rhoSetoid M w0) d)
        exact (supports_rhoQuotModel_iff hw0 hRho ht φ).2 hφ
  | t, g, ht, .inqExists x φ => by
      constructor
      · rintro ⟨d, hd⟩
        refine ⟨Quotient.mk (rhoSetoid M w0) d, ?_⟩
        simpa [liftAssign_update] using
          (supports_rhoQuotModel_iff hw0 hRho ht φ).1 hd
      · rintro ⟨qd, hqd⟩
        let d : M.D := Quotient.out qd
        have hRep : Quotient.mk (rhoSetoid M w0) d = qd := Quotient.out_eq qd
        refine ⟨d, ?_⟩
        have hφ :
            supports (rhoQuotModel M w0) t
              (liftAssign M w0 (Assignment.update g x d)) φ := by
          simpa [liftAssign_update, d, hRep] using hqd
        exact (supports_rhoQuotModel_iff hw0 hRho ht φ).2 hφ

theorem gammaNC_entails_rhoRigidEq_imp_theta :
    entails GammaNC (.imp rhoRigidEq theta) := by
  intro M s g hGamma
  intro t ht hRho
  by_cases hEmpty : t = ∅
  · simpa [hEmpty] using supports_empty M g theta
  · rcases Set.nonempty_iff_ne_empty.mpr hEmpty with ⟨w0, hw0⟩
    have hGammaQ : ∀ φ, φ ∈ GammaNC →
        supports (rhoQuotModel M w0) t (liftAssign M w0 g) φ := by
      intro φ hφ
      have hOrig : supports M t g φ :=
        supports_mono M (hGamma φ hφ) ht
      exact (supports_rhoQuotModel_iff (M := M) (s := t) (w0 := w0) hw0
        (gρ := g) hRho (Subset.rfl) φ).1 hOrig
    have hThetaQ :
        supports (rhoQuotModel M w0) t (liftAssign M w0 g) theta :=
      gammaNC_idEntails_theta
        (M := rhoQuotModel M w0)
        (rhoQuotModel_isIdModel M w0)
        t
        (liftAssign M w0 g)
        hGammaQ
    exact (supports_rhoQuotModel_iff (M := M) (s := t) (w0 := w0) hw0
      (gρ := g) hRho (Subset.rfl) theta).2 hThetaQ

theorem no_finite_subset_entails_rhoRigidEq_imp_theta :
    ¬ ∃ Γ0 : Finset (Formula SigmaAB),
      (∀ φ, φ ∈ Γ0 → φ ∈ GammaNC) ∧
        entails (↑Γ0 : Set (Formula SigmaAB)) (.imp rhoRigidEq theta) := by
  classical
  intro h
  rcases h with ⟨Γ0, hsub, hEnt⟩
  let m := Γ0.sum formulaSize
  let g : Assignment (Fin (m + 1)) := fun _ => ⟨0, Nat.succ_pos _⟩
  have hCounter := finite_gammaNC_countermodel Γ0 hsub
  rcases hCounter with ⟨hAll, hNotTheta⟩
  have hImp :
      supports (canonicalFull (Fin (m + 1))) Set.univ g (.imp rhoRigidEq theta) :=
    hEnt (canonicalFull (Fin (m + 1))) Set.univ g (by
      intro φ hφ
      exact hAll φ hφ)
  have hTheta :
      supports (canonicalFull (Fin (m + 1))) Set.univ g theta :=
    hImp Set.univ (Subset.rfl)
      (idModel_supports_rhoRigidEq
        (M := canonicalFull (Fin (m + 1)))
        (canonicalFull_isIdModel (Fin (m + 1)))
        Set.univ
        g)
  exact hNotTheta hTheta

theorem inqbq_not_compact :
    ∃ Γ : Set (Formula SigmaAB), ∃ ψ : Formula SigmaAB,
      entails Γ ψ ∧
      ¬ ∃ Γ0 : Finset (Formula SigmaAB),
        (∀ φ, φ ∈ Γ0 → φ ∈ Γ) ∧ entails (↑Γ0 : Set (Formula SigmaAB)) ψ := by
  refine ⟨GammaNC, .imp rhoRigidEq theta, gammaNC_entails_rhoRigidEq_imp_theta, ?_⟩
  exact no_finite_subset_entails_rhoRigidEq_imp_theta

end InqBQ
end HeytingLean
