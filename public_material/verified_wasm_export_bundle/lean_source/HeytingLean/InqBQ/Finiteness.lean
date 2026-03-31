import HeytingLean.InqBQ.FullModels
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Option
import Mathlib.SetTheory.Cardinal.Arithmetic

namespace HeytingLean
namespace InqBQ

open Set
open SigmaAB

/-- Syntactic inequality. -/
def neq {sig : Signature} (t u : Term sig) : Formula sig :=
  Formula.neg (.eq t u)

/-- The finiteness sentence from the paper. -/
def etaAntecedent : Formula SigmaAB :=
  .conj (Formula.dependence termA termB)
    (.conj (Formula.dependence termB termA)
      (.inqExists 0 (neq (.var 0) termB)))

def eta : Formula SigmaAB :=
  .imp etaAntecedent (.inqExists 0 (neq (.var 0) termA))

/-- The non-fullness sentence from the paper. -/
def theta : Formula SigmaAB :=
  .inqExists 0 (.inqExists 1
    (Formula.neg (.conj (.eq (.var 0) termA) (.eq (.var 1) termB))))

variable {M : InfoModel SigmaAB}

/-- Domain of a binary relation. -/
def dom (R : Set (M.D × M.D)) : Set M.D :=
  { d | ∃ e, (d, e) ∈ R }

/-- Range of a binary relation. -/
def ran (R : Set (M.D × M.D)) : Set M.D :=
  { e | ∃ d, (d, e) ∈ R }

/-- Functionality of a binary relation. -/
def RelIsFunction (R : Set (M.D × M.D)) : Prop :=
  ∀ ⦃d e₁ e₂ : M.D⦄, (d, e₁) ∈ R → (d, e₂) ∈ R → e₁ = e₂

/-- Injectivity of a binary relation viewed as a partial function. -/
def RelIsInjective (R : Set (M.D × M.D)) : Prop :=
  ∀ ⦃d₁ d₂ e : M.D⦄, (d₁, e) ∈ R → (d₂, e) ∈ R → d₁ = d₂

/-- Graph of an endomap. -/
def graph (f : M.D → M.D) : Set (M.D × M.D) :=
  { p | p.2 = f p.1 }

@[simp] theorem denote_termA (w : M.W) (g : Assignment M.D) :
    denote M w g termA = M.nonrigidInterp w ABConst.a noArgs := by
  unfold SigmaAB.termA SigmaAB.noArgs denote
  congr
  ext i
  exact Fin.elim0 i

@[simp] theorem denote_termB (w : M.W) (g : Assignment M.D) :
    denote M w g termB = M.nonrigidInterp w ABConst.b noArgs := by
  unfold SigmaAB.termB SigmaAB.noArgs denote
  congr
  ext i
  exact Fin.elim0 i

theorem supports_pair_eq_iff
    (hid : M.isIdModel) (t : Set M.W) (g : Assignment M.D) (d e : M.D) :
    supports M t ((Assignment.update g 0 d).update 1 e)
      (.conj (.eq (.var 0) termA) (.eq (.var 1) termB)) ↔
      ∀ w, w ∈ t → associatedPair M w = (d, e) := by
  constructor
  · intro h w hw
    rcases h with ⟨h0, h1⟩
    apply Prod.ext
    · have hEq : d = M.nonrigidInterp w ABConst.a noArgs := by
        exact (hid w d (M.nonrigidInterp w ABConst.a noArgs)).1 (by
          simpa [associatedPair, denote] using h0 w hw)
      exact hEq.symm
    · have hEq : e = M.nonrigidInterp w ABConst.b noArgs := by
        exact (hid w e (M.nonrigidInterp w ABConst.b noArgs)).1 (by
          simpa [associatedPair, denote] using h1 w hw)
      exact hEq.symm
  · intro h
    refine ⟨?_, ?_⟩
    · intro w hw
      simpa [denote, Assignment.update] using
        (hid w d (M.nonrigidInterp w ABConst.a noArgs)).2 (by
          simpa [associatedPair] using (congrArg Prod.fst (h w hw)).symm)
    · intro w hw
      simpa [denote, Assignment.update] using
        (hid w e (M.nonrigidInterp w ABConst.b noArgs)).2 (by
          simpa [associatedPair] using (congrArg Prod.snd (h w hw)).symm)

theorem supports_neg_pair_iff_missing
    (hid : M.isIdModel) (g : Assignment M.D) (d e : M.D) :
    supports M Set.univ ((Assignment.update g 0 d).update 1 e)
      (Formula.neg (.conj (.eq (.var 0) termA) (.eq (.var 1) termB))) ↔
      (d, e) ∉ associatedRelation M Set.univ := by
  constructor
  · intro hNeg hmem
    rcases hmem with ⟨w, -, hw⟩
    have hPair :
        supports M ({w} : Set M.W) ((Assignment.update g 0 d).update 1 e)
          (.conj (.eq (.var 0) termA) (.eq (.var 1) termB)) := by
      apply (supports_pair_eq_iff hid ({w} : Set M.W) g d e).2
      intro w' hw'
      have hw'Eq : w' = w := by simpa using hw'
      simpa [hw'Eq] using hw
    have hBot := hNeg ({w} : Set M.W) (by intro u hu; simp) hPair
    have hwSingleton : w ∈ ({w} : Set M.W) := by
      change w = w
      rfl
    have hEmpty : ({w} : Set M.W) = ∅ := hBot
    have : w ∈ (∅ : Set M.W) := by
      simpa [hEmpty] using hwSingleton
    simpa using this
  · intro hMiss
    intro t ht hPair
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hAssoc : associatedPair M w = (d, e) :=
      (supports_pair_eq_iff hid t g d e).1 hPair w hw
    exact hMiss ⟨w, by simp, hAssoc⟩

theorem theta_captures_nonfullness
    (hid : M.isIdModel) (g : Assignment M.D) :
    globallySupports M g theta ↔ ¬ isFull M := by
  constructor
  · intro hTheta hFull
    rcases hTheta with ⟨d, e, hNeg⟩
    have hMiss : (d, e) ∉ associatedRelation M Set.univ :=
      (supports_neg_pair_iff_missing hid g d e).1 hNeg
    have : (d, e) ∈ associatedRelation M Set.univ := by
      rw [hFull]
      simp
    exact hMiss this
  · intro hNotFull
    have hMissing : ∃ p : M.D × M.D, p ∉ associatedRelation M Set.univ := by
      classical
      by_contra hNoMissing
      apply hNotFull
      unfold isFull
      ext p
      constructor
      · intro hp
        simp
      · intro hpUniv
        by_contra hpRel
        exact hNoMissing ⟨p, hpRel⟩
    rcases hMissing with ⟨p, hp⟩
    rcases p with ⟨d, e⟩
    refine ⟨d, e, ?_⟩
    exact (supports_neg_pair_iff_missing hid g d e).2 hp

theorem supports_identifyA_iff
    (hid : M.isIdModel) (s : Set M.W) (g : Assignment M.D) :
    supports M s g (Formula.identify termA) ↔
      ∃ d : M.D, ∀ w, w ∈ s → M.nonrigidInterp w ABConst.a noArgs = d := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    intro w hw
    have hEq : d = M.nonrigidInterp w ABConst.a noArgs := by
      exact (hid w d (M.nonrigidInterp w ABConst.a noArgs)).1 (by
        simpa [Formula.identify, denote] using hd w hw)
    exact hEq.symm
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    intro w hw
    simpa [denote, Assignment.update] using
      (hid w d (M.nonrigidInterp w ABConst.a noArgs)).2 (by
        simpa using (hd w hw).symm)

theorem supports_identifyB_iff
    (hid : M.isIdModel) (s : Set M.W) (g : Assignment M.D) :
    supports M s g (Formula.identify termB) ↔
      ∃ e : M.D, ∀ w, w ∈ s → M.nonrigidInterp w ABConst.b noArgs = e := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    intro w hw
    have hEq : e = M.nonrigidInterp w ABConst.b noArgs := by
      exact (hid w e (M.nonrigidInterp w ABConst.b noArgs)).1 (by
        simpa [Formula.identify, denote] using he w hw)
    exact hEq.symm
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    intro w hw
    simpa [denote, Assignment.update] using
      (hid w e (M.nonrigidInterp w ABConst.b noArgs)).2 (by
        simpa using (he w hw).symm)

theorem supports_dep_ab
    (hid : M.isIdModel) (s : Set M.W) (g : Assignment M.D) :
    supports M s g (Formula.dependence termA termB) ↔
      RelIsFunction (associatedRelation M s) := by
  constructor
  · intro hdep d e₁ e₂ h1 h2
    rcases h1 with ⟨w1, hw1, hw1pair⟩
    rcases h2 with ⟨w2, hw2, hw2pair⟩
    let t : Set M.W := ({w1} : Set M.W) ∪ ({w2} : Set M.W)
    have htt : t ⊆ s := by
      intro w hw
      rcases hw with rfl | rfl <;> assumption
    have hIdA : supports M t g (Formula.identify termA) := by
      refine (supports_identifyA_iff hid t g).2 ⟨d, ?_⟩
      intro w hw
      rcases hw with rfl | rfl
      · simpa [associatedPair] using congrArg Prod.fst hw1pair
      · simpa [associatedPair] using congrArg Prod.fst hw2pair
    have hIdB := hdep t htt hIdA
    rcases (supports_identifyB_iff hid t g).1 hIdB with ⟨e, he⟩
    have he1 : e₁ = e := by
      calc
        e₁ = M.nonrigidInterp w1 ABConst.b noArgs := by
          simpa [associatedPair] using (congrArg Prod.snd hw1pair).symm
        _ = e := he w1 (by simp [t])
    have he2 : e₂ = e := by
      calc
        e₂ = M.nonrigidInterp w2 ABConst.b noArgs := by
          simpa [associatedPair] using (congrArg Prod.snd hw2pair).symm
        _ = e := he w2 (by simp [t])
    exact he1.trans he2.symm
  · intro hfun
    intro t htt hIdA
    by_cases ht : t = ∅
    · simpa [ht] using supports_empty M g (Formula.identify termB)
    · rcases Set.nonempty_iff_ne_empty.mpr ht with ⟨w0, hw0⟩
      rcases (supports_identifyA_iff hid t g).1 hIdA with ⟨d, hd⟩
      refine (supports_identifyB_iff hid t g).2 ⟨M.nonrigidInterp w0 ABConst.b noArgs, ?_⟩
      intro w hw
      have hw0rel : (d, M.nonrigidInterp w0 ABConst.b noArgs) ∈ associatedRelation M s := by
        refine ⟨w0, htt hw0, ?_⟩
        simp [associatedPair, hd w0 hw0]
      have hwrel : (d, M.nonrigidInterp w ABConst.b noArgs) ∈ associatedRelation M s := by
        refine ⟨w, htt hw, ?_⟩
        simp [associatedPair, hd w hw]
      exact hfun hwrel hw0rel

theorem supports_dep_ba
    (hid : M.isIdModel) (s : Set M.W) (g : Assignment M.D) :
    supports M s g (Formula.dependence termB termA) ↔
      RelIsInjective (associatedRelation M s) := by
  constructor
  · intro hdep d₁ d₂ e h1 h2
    rcases h1 with ⟨w1, hw1, hw1pair⟩
    rcases h2 with ⟨w2, hw2, hw2pair⟩
    let t : Set M.W := ({w1} : Set M.W) ∪ ({w2} : Set M.W)
    have htt : t ⊆ s := by
      intro w hw
      rcases hw with rfl | rfl <;> assumption
    have hIdB : supports M t g (Formula.identify termB) := by
      refine (supports_identifyB_iff hid t g).2 ⟨e, ?_⟩
      intro w hw
      rcases hw with rfl | rfl
      · simpa [associatedPair] using congrArg Prod.snd hw1pair
      · simpa [associatedPair] using congrArg Prod.snd hw2pair
    have hIdA := hdep t htt hIdB
    rcases (supports_identifyA_iff hid t g).1 hIdA with ⟨d, hd⟩
    have hd1 : d₁ = d := by
      calc
        d₁ = M.nonrigidInterp w1 ABConst.a noArgs := by
          simpa [associatedPair] using (congrArg Prod.fst hw1pair).symm
        _ = d := hd w1 (by simp [t])
    have hd2 : d₂ = d := by
      calc
        d₂ = M.nonrigidInterp w2 ABConst.a noArgs := by
          simpa [associatedPair] using (congrArg Prod.fst hw2pair).symm
        _ = d := hd w2 (by simp [t])
    exact hd1.trans hd2.symm
  · intro hinj
    intro t htt hIdB
    by_cases ht : t = ∅
    · simpa [ht] using supports_empty M g (Formula.identify termA)
    · rcases Set.nonempty_iff_ne_empty.mpr ht with ⟨w0, hw0⟩
      rcases (supports_identifyB_iff hid t g).1 hIdB with ⟨e, he⟩
      refine (supports_identifyA_iff hid t g).2 ⟨M.nonrigidInterp w0 ABConst.a noArgs, ?_⟩
      intro w hw
      have hw0rel : (M.nonrigidInterp w0 ABConst.a noArgs, e) ∈ associatedRelation M s := by
        refine ⟨w0, htt hw0, ?_⟩
        simp [associatedPair, he w0 hw0]
      have hwrel : (M.nonrigidInterp w ABConst.a noArgs, e) ∈ associatedRelation M s := by
        refine ⟨w, htt hw, ?_⟩
        simp [associatedPair, he w hw]
      exact hinj hwrel hw0rel

theorem supports_exists_neq_a
    (hid : M.isIdModel) (s : Set M.W) (g : Assignment M.D) :
    supports M s g (.inqExists 0 (neq (.var 0) termA)) ↔
      ∃ d : M.D, d ∉ dom (associatedRelation M s) := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    rintro ⟨e, hmem⟩
    rcases hmem with ⟨w, hw, hwpair⟩
    have hEq : supports M ({w} : Set M.W) ((Assignment.update g 0 d))
        (.eq (.var 0) termA) := by
      intro w' hw'
      have hw'Eq : w' = w := by simpa using hw'
      simpa [denote, Assignment.update, hw'Eq] using
        (hid w d (M.nonrigidInterp w ABConst.a noArgs)).2 (by
          simpa [associatedPair] using (congrArg Prod.fst hwpair).symm)
    have hBot := hd ({w} : Set M.W) (by
      intro u hu
      have huEq : u = w := by simpa using hu
      simpa [huEq] using hw) hEq
    have : w ∈ (∅ : Set M.W) := by
      have hwSingleton : w ∈ ({w} : Set M.W) := by simp
      have hEmpty : ({w} : Set M.W) = ∅ := hBot
      simpa [hEmpty] using hwSingleton
    simpa using this
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    intro t htt hEq
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hLocal : M.localEq w d (M.nonrigidInterp w ABConst.a noArgs) := by
      simpa [denote] using hEq w hw
    have hdEq : d = M.nonrigidInterp w ABConst.a noArgs := (hid w d _).1 hLocal
    apply hd
    refine ⟨M.nonrigidInterp w ABConst.b noArgs, ⟨w, htt hw, ?_⟩⟩
    simpa [associatedPair, hdEq]

theorem supports_exists_neq_b
    (hid : M.isIdModel) (s : Set M.W) (g : Assignment M.D) :
    supports M s g (.inqExists 0 (neq (.var 0) termB)) ↔
      ∃ e : M.D, e ∉ ran (associatedRelation M s) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    rintro ⟨d, hmem⟩
    rcases hmem with ⟨w, hw, hwpair⟩
    have hEq : supports M ({w} : Set M.W) ((Assignment.update g 0 e))
        (.eq (.var 0) termB) := by
      intro w' hw'
      have hw'Eq : w' = w := by simpa using hw'
      simpa [denote, Assignment.update, hw'Eq] using
        (hid w e (M.nonrigidInterp w ABConst.b noArgs)).2 (by
          simpa [associatedPair] using (congrArg Prod.snd hwpair).symm)
    have hBot := he ({w} : Set M.W) (by
      intro u hu
      have huEq : u = w := by simpa using hu
      simpa [huEq] using hw) hEq
    have : w ∈ (∅ : Set M.W) := by
      have hwSingleton : w ∈ ({w} : Set M.W) := by simp
      have hEmpty : ({w} : Set M.W) = ∅ := hBot
      simpa [hEmpty] using hwSingleton
    simpa using this
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    intro t htt hEq
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hLocal : M.localEq w e (M.nonrigidInterp w ABConst.b noArgs) := by
      simpa [denote] using hEq w hw
    have heEq : e = M.nonrigidInterp w ABConst.b noArgs := (hid w e _).1 hLocal
    apply he
    refine ⟨M.nonrigidInterp w ABConst.a noArgs, ⟨w, htt hw, ?_⟩⟩
    simpa [associatedPair, heEq]

theorem not_supports_exists_neq_a
    (hid : M.isIdModel) (s : Set M.W) (g : Assignment M.D) :
    ¬ supports M s g (.inqExists 0 (neq (.var 0) termA)) ↔
      dom (associatedRelation M s) = Set.univ := by
  constructor
  · intro hNo
    ext d
    constructor
    · intro _
      simp
    · intro _
      by_contra hd
      exact hNo ((supports_exists_neq_a hid s g).2 ⟨d, hd⟩)
  · intro hDom hYes
    rcases (supports_exists_neq_a hid s g).1 hYes with ⟨d, hd⟩
    have : d ∈ dom (associatedRelation M s) := by simpa [hDom]
    exact hd this

theorem graph_isFunction (f : M.D → M.D) : RelIsFunction (graph (M := M) f) := by
  intro d e₁ e₂ h1 h2
  simpa [graph] using h1.trans h2.symm

theorem graph_isInjective (f : M.D → M.D) (hf : Function.Injective f) :
    RelIsInjective (graph (M := M) f) := by
  intro d₁ d₂ e h1 h2
  apply hf
  simpa [graph] using h1.symm.trans h2

theorem dom_graph (f : M.D → M.D) :
    dom (graph (M := M) f) = Set.univ := by
  ext d
  constructor
  · intro _
    simp
  · intro _
    refine ⟨f d, ?_⟩
    simp [graph]

theorem ran_graph (f : M.D → M.D) :
    ran (graph (M := M) f) = Set.range f := by
  ext e
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d, by simpa [graph] using hd.symm⟩
  · rintro ⟨d, rfl⟩
    exact ⟨d, by simp [graph]⟩

noncomputable def relationFun
    (R : Set (M.D × M.D)) (hfun : RelIsFunction R) (hdom : dom R = Set.univ) :
    M.D → M.D :=
  fun d => Classical.choose (show ∃ e, (d, e) ∈ R from by
    have hd : d ∈ dom R := by simpa [hdom]
    exact hd)

theorem relationFun_spec
    (R : Set (M.D × M.D)) (hfun : RelIsFunction R) (hdom : dom R = Set.univ) (d : M.D) :
    (d, relationFun (M := M) R hfun hdom d) ∈ R :=
  Classical.choose_spec (show ∃ e, (d, e) ∈ R from by
    have hd : d ∈ dom R := by simpa [hdom]
    exact hd)

theorem relationFun_injective
    (R : Set (M.D × M.D)) (hfun : RelIsFunction R) (hinj : RelIsInjective R)
    (hdom : dom R = Set.univ) :
    Function.Injective (relationFun (M := M) R hfun hdom) := by
  intro d₁ d₂ hEq
  apply hinj
  · exact relationFun_spec (M := M) R hfun hdom d₁
  · simpa [hEq] using relationFun_spec (M := M) R hfun hdom d₂

noncomputable def optionEquivSelf (α : Type*) [Infinite α] : Option α ≃ α :=
  Classical.choice <| Cardinal.eq.mp <| by
    rw [Cardinal.mk_option, Cardinal.mk_add_one_eq]

noncomputable def infiniteEndomap (α : Type*) [Infinite α] : α → α :=
  fun a => optionEquivSelf α (some a)

theorem infiniteEndomap_injective (α : Type*) [Infinite α] :
    Function.Injective (infiniteEndomap α) :=
  (optionEquivSelf α).injective.comp (@Option.some_injective α)

theorem infiniteEndomap_not_surjective (α : Type*) [Infinite α] :
    ¬ Function.Surjective (infiniteEndomap α) := by
  intro hsurj
  rcases hsurj (optionEquivSelf α none) with ⟨a, ha⟩
  have : (some a : Option α) = none := (optionEquivSelf α).injective ha
  simp at this

noncomputable def chosenWorldOfPair (hfull : isFull M) (p : M.D × M.D) : M.W :=
  Classical.choose <| by
    have hp : p ∈ associatedRelation M Set.univ := by
      rw [hfull]
      simp
    rcases hp with ⟨w, -, hw⟩
    exact ⟨w, hw⟩

theorem chosenWorldOfPair_spec (hfull : isFull M) (p : M.D × M.D) :
    associatedPair M (chosenWorldOfPair (M := M) hfull p) = p :=
  Classical.choose_spec <| by
    have hp : p ∈ associatedRelation M Set.univ := by
      rw [hfull]
      simp
    rcases hp with ⟨w, -, hw⟩
    exact ⟨w, hw⟩

noncomputable def stateOfRelation (hfull : isFull M) (R : Set (M.D × M.D)) : Set M.W :=
  { w | ∃ p, p ∈ R ∧ w = chosenWorldOfPair (M := M) hfull p }

theorem stateOfRelation_subset_univ (hfull : isFull M) (R : Set (M.D × M.D)) :
    stateOfRelation (M := M) hfull R ⊆ Set.univ := by
  intro w hw
  simp

theorem associatedRelation_stateOfRelation (hfull : isFull M) (R : Set (M.D × M.D)) :
    associatedRelation M (stateOfRelation (M := M) hfull R) = R := by
  ext p
  constructor
  · rintro ⟨w, hw, hwp⟩
    rcases hw with ⟨p', hp'R, rfl⟩
    have hpEq : p = p' := by
      simpa [chosenWorldOfPair_spec (M := M) hfull p'] using hwp.symm
    simpa [hpEq] using hp'R
  · intro hp
    refine ⟨chosenWorldOfPair (M := M) hfull p, ?_, chosenWorldOfPair_spec (M := M) hfull p⟩
    exact ⟨p, hp, rfl⟩

theorem eta_captures_finiteness
    (hfull : isFull M) (hid : M.isIdModel) (g : Assignment M.D) :
    globallySupports M g eta ↔ Finite M.D := by
  constructor
  · intro hEta
    by_contra hNotFinite
    letI : Infinite M.D := not_finite_iff_infinite.mp hNotFinite
    let f : M.D → M.D := infiniteEndomap M.D
    let s : Set M.W := stateOfRelation (M := M) hfull (graph (M := M) f)
    have hs : s ⊆ Set.univ := stateOfRelation_subset_univ (M := M) hfull (graph (M := M) f)
    have hRel : associatedRelation M s = graph (M := M) f :=
      associatedRelation_stateOfRelation (M := M) hfull (graph (M := M) f)
    have hAnte : supports M s g etaAntecedent := by
      refine ⟨?_, ?_⟩
      · exact (supports_dep_ab hid s g).2 (by simpa [hRel] using graph_isFunction (M := M) f)
      · refine ⟨?_, ?_⟩
        · exact (supports_dep_ba hid s g).2 (by
            simpa [hRel] using graph_isInjective (M := M) f (infiniteEndomap_injective M.D))
        · have hMissing : ∃ e : M.D, e ∉ Set.range f := by
            by_contra hNo
            apply infiniteEndomap_not_surjective M.D
            intro e
            by_contra he
            exact hNo ⟨e, he⟩
          rcases hMissing with ⟨e, he⟩
          exact (supports_exists_neq_b hid s g).2 ⟨e, by simpa [hRel, ran_graph] using he⟩
    have hNoCons : ¬ supports M s g (.inqExists 0 (neq (.var 0) termA)) := by
      rw [not_supports_exists_neq_a hid s g]
      simpa [hRel, dom_graph]
    exact hNoCons (hEta s hs hAnte)
  · intro hFinite
    intro s hs hAnte
    rcases hAnte with ⟨hFun, hRest⟩
    rcases hRest with ⟨hInj, hRan⟩
    have hRfun : RelIsFunction (associatedRelation M s) := (supports_dep_ab hid s g).1 hFun
    have hRinj : RelIsInjective (associatedRelation M s) := (supports_dep_ba hid s g).1 hInj
    rcases (supports_exists_neq_b hid s g).1 hRan with ⟨e, heMiss⟩
    by_cases hCons : supports M s g (.inqExists 0 (neq (.var 0) termA))
    · exact hCons
    · have hDom : dom (associatedRelation M s) = Set.univ :=
          (not_supports_exists_neq_a hid s g).1 hCons
      let f := relationFun (M := M) (associatedRelation M s) hRfun hDom
      have hfinj : Function.Injective f :=
        relationFun_injective (M := M) (associatedRelation M s) hRfun hRinj hDom
      letI : Finite M.D := hFinite
      have hsurj : Function.Surjective f := Finite.surjective_of_injective hfinj
      rcases hsurj e with ⟨d, hde⟩
      exfalso
      apply heMiss
      refine ⟨d, ?_⟩
      rw [← hde]
      exact relationFun_spec (M := M) (associatedRelation M s) hRfun hDom d

end InqBQ
end HeytingLean
