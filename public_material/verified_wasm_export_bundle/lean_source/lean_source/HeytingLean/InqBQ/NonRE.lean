import HeytingLean.InqBQ.NonCompactness

/-!
# InqBQ non-r.e. reduction fence

This module closes the InqBQ side of the finite-validity reduction from the paper:
it builds the generalized canonical full id-model over an arbitrary classical
signature, proves the `η → (α ⩾ θ)` reduction theorem on the id-valid surface,
and intentionally stops there.

The final theorem that InqBQ validities are not recursively enumerable is
*not* stated here, because the local codebase does not currently expose a
verified axiom-free Trakhtenbrot theorem to discharge the remaining
computability-theoretic step.
-/

namespace HeytingLean
namespace InqBQ

open Classical
open Set

/-- Add the two non-rigid nullary symbols `a` and `b` to an existing signature. -/
def ABSignature (sig : Signature) : Signature where
  PredSym := sig.PredSym
  RigidFun := sig.RigidFun
  NonRigidFun := sig.NonRigidFun ⊕ ABConst
  predArity := sig.predArity
  rigidArity := sig.rigidArity
  nonrigidArity
    | Sum.inl f => sig.nonrigidArity f
    | Sum.inr _ => 0

namespace ABSignature

variable {sig : Signature}

def noArgs {α : Type*} : Fin 0 → α := Fin.elim0

/-- The added non-rigid constant `a`. -/
def termA : Term (ABSignature sig) :=
  .nonrigidApp (Sum.inr ABConst.a) noArgs

/-- The added non-rigid constant `b`. -/
def termB : Term (ABSignature sig) :=
  .nonrigidApp (Sum.inr ABConst.b) noArgs

/-- Embed a base-signature term into the `Σ + {a,b}` extension. -/
def embedTerm : Term sig → Term (ABSignature sig)
  | .var x => .var x
  | .rigidApp f args => .rigidApp f (fun i => embedTerm (args i))
  | .nonrigidApp f args => .nonrigidApp (Sum.inl f) (fun i => embedTerm (args i))

/-- Embed a base-signature formula into the `Σ + {a,b}` extension. -/
def embedFormula : Formula sig → Formula (ABSignature sig)
  | .pred P args => .pred P (fun i => embedTerm (args i))
  | .eq t u => .eq (embedTerm t) (embedTerm u)
  | .bot => .bot
  | .conj φ ψ => .conj (embedFormula φ) (embedFormula ψ)
  | .inqDisj φ ψ => .inqDisj (embedFormula φ) (embedFormula ψ)
  | .imp φ ψ => .imp (embedFormula φ) (embedFormula ψ)
  | .forall_ x φ => .forall_ x (embedFormula φ)
  | .inqExists x φ => .inqExists x (embedFormula φ)

theorem embedFormula_isClassical {φ : Formula sig} :
    Formula.isClassical φ → Formula.isClassical (embedFormula φ) := by
  induction φ with
  | pred P args =>
      intro _
      trivial
  | eq t u =>
      intro _
      trivial
  | bot =>
      intro _
      trivial
  | conj φ ψ ihφ ihψ =>
      intro hClass
      rcases hClass with ⟨hφ, hψ⟩
      exact ⟨ihφ hφ, ihψ hψ⟩
  | inqDisj φ ψ =>
      intro hClass
      cases hClass
  | imp φ ψ ihφ ihψ =>
      intro hClass
      rcases hClass with ⟨hφ, hψ⟩
      exact ⟨ihφ hφ, ihψ hψ⟩
  | forall_ x φ ih =>
      intro hClass
      exact ih hClass
  | inqExists x φ =>
      intro hClass
      cases hClass

end ABSignature

/-- World-independent classical structures over an InqBQ signature. -/
structure ClassicalStructure (sig : Signature) where
  D : Type
  hD : Nonempty D
  predInterp :
    (P : sig.PredSym) → (Fin (sig.predArity P) → D) → Prop
  rigidInterp :
    (f : sig.RigidFun) → (Fin (sig.rigidArity f) → D) → D
  nonrigidInterp :
    (f : sig.NonRigidFun) → (Fin (sig.nonrigidArity f) → D) → D

namespace ClassicalStructure

variable {sig : Signature}

/-- Term denotation in a world-independent classical structure. -/
def denote (S : ClassicalStructure sig) (g : Assignment S.D) : Term sig → S.D
  | .var x => g x
  | .rigidApp f args => S.rigidInterp f (fun i => denote S g (args i))
  | .nonrigidApp f args => S.nonrigidInterp f (fun i => denote S g (args i))

/-- Classical truth of an InqBQ formula in a world-independent structure. -/
def satisfies (S : ClassicalStructure sig) (g : Assignment S.D) : Formula sig → Prop
  | .pred P ts =>
      S.predInterp P (fun i => denote S g (ts i))
  | .eq t u =>
      denote S g t = denote S g u
  | .bot =>
      False
  | .conj φ ψ =>
      satisfies S g φ ∧ satisfies S g ψ
  | .inqDisj φ ψ =>
      satisfies S g φ ∨ satisfies S g ψ
  | .imp φ ψ =>
      satisfies S g φ → satisfies S g ψ
  | .forall_ x φ =>
      ∀ d : S.D, satisfies S (Assignment.update g x d) φ
  | .inqExists x φ =>
      ∃ d : S.D, satisfies S (Assignment.update g x d) φ

end ClassicalStructure

section GenericAB

variable {sig : Signature}

open ABSignature

/-- The pair selected by the added non-rigid constants at a world. -/
def associatedPairAB (M : InfoModel (ABSignature sig)) (w : M.W) : M.D × M.D :=
  (M.nonrigidInterp w (Sum.inr ABConst.a) noArgs,
    M.nonrigidInterp w (Sum.inr ABConst.b) noArgs)

/-- The relation induced by a state through the added constants `a,b`. -/
def associatedRelationAB (M : InfoModel (ABSignature sig)) (s : Set M.W) : Set (M.D × M.D) :=
  { p | ∃ w ∈ s, associatedPairAB M w = p }

/-- Fullness of a state relative to the added constants `a,b`. -/
def fullOnAB (M : InfoModel (ABSignature sig)) (s : Set M.W) : Prop :=
  associatedRelationAB M s = Set.univ

/-- Domain of a binary relation. -/
def relDom {D : Type*} (R : Set (D × D)) : Set D :=
  { d | ∃ e, (d, e) ∈ R }

/-- Range of a binary relation. -/
def relRan {D : Type*} (R : Set (D × D)) : Set D :=
  { e | ∃ d, (d, e) ∈ R }

/-- Functionality of a binary relation. -/
def RelIsFunctionAB {D : Type*} (R : Set (D × D)) : Prop :=
  ∀ ⦃d e₁ e₂ : D⦄, (d, e₁) ∈ R → (d, e₂) ∈ R → e₁ = e₂

/-- Injectivity of a binary relation viewed as a partial function. -/
def RelIsInjectiveAB {D : Type*} (R : Set (D × D)) : Prop :=
  ∀ ⦃d₁ d₂ e : D⦄, (d₁, e) ∈ R → (d₂, e) ∈ R → d₁ = d₂

/-- Graph of an endomap. -/
def relGraph {D : Type*} (f : D → D) : Set (D × D) :=
  { p | p.2 = f p.1 }

/-- The extended-signature finiteness sentence. -/
def etaAntecedentAB : Formula (ABSignature sig) :=
  .conj (Formula.dependence termA termB)
    (.conj (Formula.dependence termB termA)
      (.inqExists 0 (neq (.var 0) termB)))

/-- The extended-signature finiteness sentence `η`. -/
def etaAB : Formula (ABSignature sig) :=
  .imp etaAntecedentAB (.inqExists 0 (neq (.var 0) termA))

/-- The extended-signature non-fullness sentence `θ`. -/
def thetaAB : Formula (ABSignature sig) :=
  .inqExists 0 (.inqExists 1
    (Formula.neg (.conj (.eq (.var 0) termA) (.eq (.var 1) termB))))

variable {M : InfoModel (ABSignature sig)}

@[simp] theorem denote_termA_AB (w : M.W) (g : Assignment M.D) :
    denote M w g termA = M.nonrigidInterp w (Sum.inr ABConst.a) noArgs := by
  unfold ABSignature.termA ABSignature.noArgs denote
  congr
  ext i
  exact Fin.elim0 i

@[simp] theorem denote_termB_AB (w : M.W) (g : Assignment M.D) :
    denote M w g termB = M.nonrigidInterp w (Sum.inr ABConst.b) noArgs := by
  unfold ABSignature.termB ABSignature.noArgs denote
  congr
  ext i
  exact Fin.elim0 i

theorem supports_pair_eq_iff_AB
    (hid : M.isIdModel) (s : Set M.W) (g : Assignment M.D) (d e : M.D) :
    supports M s ((Assignment.update g 0 d).update 1 e)
      (.conj (.eq (.var 0) termA) (.eq (.var 1) termB)) ↔
      ∀ w, w ∈ s → associatedPairAB M w = (d, e) := by
  constructor
  · intro h w hw
    rcases h with ⟨h0, h1⟩
    apply Prod.ext
    · have hEq : d = M.nonrigidInterp w (Sum.inr ABConst.a) noArgs := by
        exact (hid w d _).1 (by
          simpa [associatedPairAB, denote] using h0 w hw)
      exact hEq.symm
    · have hEq : e = M.nonrigidInterp w (Sum.inr ABConst.b) noArgs := by
        exact (hid w e _).1 (by
          simpa [associatedPairAB, denote] using h1 w hw)
      exact hEq.symm
  · intro h
    refine ⟨?_, ?_⟩
    · intro w hw
      simpa [denote, Assignment.update] using
        (hid w d _).2 (by
          simpa [associatedPairAB] using (congrArg Prod.fst (h w hw)).symm)
    · intro w hw
      simpa [denote, Assignment.update] using
        (hid w e _).2 (by
          simpa [associatedPairAB] using (congrArg Prod.snd (h w hw)).symm)

theorem supports_neg_pair_iff_missing_AB
    (hid : M.isIdModel) (g : Assignment M.D) (d e : M.D) :
    supports M Set.univ ((Assignment.update g 0 d).update 1 e)
      (Formula.neg (.conj (.eq (.var 0) termA) (.eq (.var 1) termB))) ↔
      (d, e) ∉ associatedRelationAB M Set.univ := by
  constructor
  · intro hNeg hmem
    rcases hmem with ⟨w, -, hw⟩
    have hPair :
        supports M ({w} : Set M.W) ((Assignment.update g 0 d).update 1 e)
          (.conj (.eq (.var 0) termA) (.eq (.var 1) termB)) := by
      apply (supports_pair_eq_iff_AB hid ({w} : Set M.W) g d e).2
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
    have hAssoc : associatedPairAB M w = (d, e) :=
      (supports_pair_eq_iff_AB hid t g d e).1 hPair w hw
    exact hMiss ⟨w, by simp, hAssoc⟩

theorem supports_thetaAB_iff_nonfull
    (hid : M.isIdModel) (s : Set M.W) (g : Assignment M.D) :
    supports M s g thetaAB ↔ ¬ fullOnAB M s := by
  constructor
  · rintro ⟨d, e, hNeg⟩ hFull
    have hMiss : (d, e) ∉ associatedRelationAB M s := by
      intro hmem
      rcases hmem with ⟨w, hw, hpair⟩
      have hPair :
          supports M ({w} : Set M.W) ((Assignment.update g 0 d).update 1 e)
            (.conj (.eq (.var 0) termA) (.eq (.var 1) termB)) := by
        apply (supports_pair_eq_iff_AB hid ({w} : Set M.W) g d e).2
        intro w' hw'
        have hw'Eq : w' = w := by simpa using hw'
        simpa [hw'Eq] using hpair
      have hBot := hNeg ({w} : Set M.W) (by
        intro u hu
        have huEq : u = w := by simpa using hu
        simpa [huEq] using hw) hPair
      have hwSingleton : w ∈ ({w} : Set M.W) := by
        simp
      have hEmpty : ({w} : Set M.W) = ∅ := hBot
      have : w ∈ (∅ : Set M.W) := by
        simpa [hEmpty] using hwSingleton
      simpa using this
    have : (d, e) ∈ associatedRelationAB M s := by
      rw [hFull]
      simp
    exact hMiss this
  · intro hNotFull
    have hMissing : ∃ p : M.D × M.D, p ∉ associatedRelationAB M s := by
      classical
      by_contra hNoMissing
      apply hNotFull
      unfold fullOnAB
      ext p
      constructor
      · intro hp
        simp
      · intro hpUniv
        by_contra hpRel
        exact hNoMissing ⟨p, hpRel⟩
    rcases hMissing with ⟨⟨d, e⟩, hp⟩
    refine ⟨d, e, ?_⟩
    intro t ht hPair
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hAssoc : associatedPairAB M w = (d, e) :=
      (supports_pair_eq_iff_AB hid t g d e).1 hPair w hw
    exact hp ⟨w, ht hw, hAssoc⟩

theorem supports_identifyA_iff_AB
    (hid : M.isIdModel) (s : Set M.W) (g : Assignment M.D) :
    supports M s g (Formula.identify termA) ↔
      ∃ d : M.D, ∀ w, w ∈ s → M.nonrigidInterp w (Sum.inr ABConst.a) noArgs = d := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    intro w hw
    have hEq : d = M.nonrigidInterp w (Sum.inr ABConst.a) noArgs := by
      exact (hid w d _).1 (by
        simpa [Formula.identify, denote] using hd w hw)
    exact hEq.symm
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    intro w hw
    simpa [denote, Assignment.update] using
      (hid w d _).2 (by
        simpa using (hd w hw).symm)

theorem supports_identifyB_iff_AB
    (hid : M.isIdModel) (s : Set M.W) (g : Assignment M.D) :
    supports M s g (Formula.identify termB) ↔
      ∃ e : M.D, ∀ w, w ∈ s → M.nonrigidInterp w (Sum.inr ABConst.b) noArgs = e := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    intro w hw
    have hEq : e = M.nonrigidInterp w (Sum.inr ABConst.b) noArgs := by
      exact (hid w e _).1 (by
        simpa [Formula.identify, denote] using he w hw)
    exact hEq.symm
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    intro w hw
    simpa [denote, Assignment.update] using
      (hid w e _).2 (by
        simpa using (he w hw).symm)

theorem supports_dep_ab_AB
    (hid : M.isIdModel) (s : Set M.W) (g : Assignment M.D) :
    supports M s g (Formula.dependence termA termB) ↔
      RelIsFunctionAB (associatedRelationAB M s) := by
  constructor
  · intro hdep d e₁ e₂ h1 h2
    rcases h1 with ⟨w1, hw1, hw1pair⟩
    rcases h2 with ⟨w2, hw2, hw2pair⟩
    let t : Set M.W := ({w1} : Set M.W) ∪ ({w2} : Set M.W)
    have htt : t ⊆ s := by
      intro w hw
      rcases hw with rfl | rfl <;> assumption
    have hIdA : supports M t g (Formula.identify termA) := by
      refine (supports_identifyA_iff_AB hid t g).2 ⟨d, ?_⟩
      intro w hw
      rcases hw with rfl | rfl
      · simpa [associatedPairAB] using congrArg Prod.fst hw1pair
      · simpa [associatedPairAB] using congrArg Prod.fst hw2pair
    have hIdB := hdep t htt hIdA
    rcases (supports_identifyB_iff_AB hid t g).1 hIdB with ⟨e, he⟩
    have he1 : e₁ = e := by
      calc
        e₁ = M.nonrigidInterp w1 (Sum.inr ABConst.b) noArgs := by
          simpa [associatedPairAB] using (congrArg Prod.snd hw1pair).symm
        _ = e := he w1 (by simp [t])
    have he2 : e₂ = e := by
      calc
        e₂ = M.nonrigidInterp w2 (Sum.inr ABConst.b) noArgs := by
          simpa [associatedPairAB] using (congrArg Prod.snd hw2pair).symm
        _ = e := he w2 (by simp [t])
    exact he1.trans he2.symm
  · intro hfun
    intro t htt hIdA
    by_cases ht : t = ∅
    · simpa [ht] using supports_empty M g (Formula.identify termB)
    · rcases Set.nonempty_iff_ne_empty.mpr ht with ⟨w0, hw0⟩
      rcases (supports_identifyA_iff_AB hid t g).1 hIdA with ⟨d, hd⟩
      refine (supports_identifyB_iff_AB hid t g).2
        ⟨M.nonrigidInterp w0 (Sum.inr ABConst.b) noArgs, ?_⟩
      intro w hw
      have hw0rel :
          (d, M.nonrigidInterp w0 (Sum.inr ABConst.b) noArgs) ∈ associatedRelationAB M s := by
        refine ⟨w0, htt hw0, ?_⟩
        simp [associatedPairAB, hd w0 hw0]
      have hwrel :
          (d, M.nonrigidInterp w (Sum.inr ABConst.b) noArgs) ∈ associatedRelationAB M s := by
        refine ⟨w, htt hw, ?_⟩
        simp [associatedPairAB, hd w hw]
      exact hfun hwrel hw0rel

theorem supports_dep_ba_AB
    (hid : M.isIdModel) (s : Set M.W) (g : Assignment M.D) :
    supports M s g (Formula.dependence termB termA) ↔
      RelIsInjectiveAB (associatedRelationAB M s) := by
  constructor
  · intro hdep d₁ d₂ e h1 h2
    rcases h1 with ⟨w1, hw1, hw1pair⟩
    rcases h2 with ⟨w2, hw2, hw2pair⟩
    let t : Set M.W := ({w1} : Set M.W) ∪ ({w2} : Set M.W)
    have htt : t ⊆ s := by
      intro w hw
      rcases hw with rfl | rfl <;> assumption
    have hIdB : supports M t g (Formula.identify termB) := by
      refine (supports_identifyB_iff_AB hid t g).2 ⟨e, ?_⟩
      intro w hw
      rcases hw with rfl | rfl
      · simpa [associatedPairAB] using congrArg Prod.snd hw1pair
      · simpa [associatedPairAB] using congrArg Prod.snd hw2pair
    have hIdA := hdep t htt hIdB
    rcases (supports_identifyA_iff_AB hid t g).1 hIdA with ⟨d, hd⟩
    have hd1 : d₁ = d := by
      calc
        d₁ = M.nonrigidInterp w1 (Sum.inr ABConst.a) noArgs := by
          simpa [associatedPairAB] using (congrArg Prod.fst hw1pair).symm
        _ = d := hd w1 (by simp [t])
    have hd2 : d₂ = d := by
      calc
        d₂ = M.nonrigidInterp w2 (Sum.inr ABConst.a) noArgs := by
          simpa [associatedPairAB] using (congrArg Prod.fst hw2pair).symm
        _ = d := hd w2 (by simp [t])
    exact hd1.trans hd2.symm
  · intro hinj
    intro t htt hIdB
    by_cases ht : t = ∅
    · simpa [ht] using supports_empty M g (Formula.identify termA)
    · rcases Set.nonempty_iff_ne_empty.mpr ht with ⟨w0, hw0⟩
      rcases (supports_identifyB_iff_AB hid t g).1 hIdB with ⟨e, he⟩
      refine (supports_identifyA_iff_AB hid t g).2
        ⟨M.nonrigidInterp w0 (Sum.inr ABConst.a) noArgs, ?_⟩
      intro w hw
      have hw0rel :
          (M.nonrigidInterp w0 (Sum.inr ABConst.a) noArgs, e) ∈ associatedRelationAB M s := by
        refine ⟨w0, htt hw0, ?_⟩
        simp [associatedPairAB, he w0 hw0]
      have hwrel :
          (M.nonrigidInterp w (Sum.inr ABConst.a) noArgs, e) ∈ associatedRelationAB M s := by
        refine ⟨w, htt hw, ?_⟩
        simp [associatedPairAB, he w hw]
      exact hinj hwrel hw0rel

theorem supports_exists_neq_a_AB
    (hid : M.isIdModel) (s : Set M.W) (g : Assignment M.D) :
    supports M s g (.inqExists 0 (neq (.var 0) termA)) ↔
      ∃ d : M.D, d ∉ relDom (associatedRelationAB M s) := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    rintro ⟨e, hmem⟩
    rcases hmem with ⟨w, hw, hwpair⟩
    have hEq :
        supports M ({w} : Set M.W) (Assignment.update g 0 d) (.eq (.var 0) termA) := by
      intro w' hw'
      have hw'Eq : w' = w := by simpa using hw'
      simpa [denote, Assignment.update, hw'Eq] using
        (hid w d _).2 (by
          simpa [associatedPairAB] using (congrArg Prod.fst hwpair).symm)
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
    have hLocal :
        M.localEq w d (M.nonrigidInterp w (Sum.inr ABConst.a) noArgs) := by
      simpa [denote] using hEq w hw
    have hdEq : d = M.nonrigidInterp w (Sum.inr ABConst.a) noArgs := (hid w d _).1 hLocal
    apply hd
    refine ⟨M.nonrigidInterp w (Sum.inr ABConst.b) noArgs, ⟨w, htt hw, ?_⟩⟩
    simpa [associatedPairAB, hdEq]

theorem supports_exists_neq_b_AB
    (hid : M.isIdModel) (s : Set M.W) (g : Assignment M.D) :
    supports M s g (.inqExists 0 (neq (.var 0) termB)) ↔
      ∃ e : M.D, e ∉ relRan (associatedRelationAB M s) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    rintro ⟨d, hmem⟩
    rcases hmem with ⟨w, hw, hwpair⟩
    have hEq :
        supports M ({w} : Set M.W) (Assignment.update g 0 e) (.eq (.var 0) termB) := by
      intro w' hw'
      have hw'Eq : w' = w := by simpa using hw'
      simpa [denote, Assignment.update, hw'Eq] using
        (hid w e _).2 (by
          simpa [associatedPairAB] using (congrArg Prod.snd hwpair).symm)
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
    have hLocal :
        M.localEq w e (M.nonrigidInterp w (Sum.inr ABConst.b) noArgs) := by
      simpa [denote] using hEq w hw
    have heEq : e = M.nonrigidInterp w (Sum.inr ABConst.b) noArgs := (hid w e _).1 hLocal
    apply he
    refine ⟨M.nonrigidInterp w (Sum.inr ABConst.a) noArgs, ⟨w, htt hw, ?_⟩⟩
    simpa [associatedPairAB, heEq]

theorem not_supports_exists_neq_a_AB
    (hid : M.isIdModel) (s : Set M.W) (g : Assignment M.D) :
    ¬ supports M s g (.inqExists 0 (neq (.var 0) termA)) ↔
      relDom (associatedRelationAB M s) = Set.univ := by
  constructor
  · intro hNo
    ext d
    constructor
    · intro _
      simp
    · intro _
      by_contra hd
      exact hNo ((supports_exists_neq_a_AB hid s g).2 ⟨d, hd⟩)
  · intro hDom hYes
    rcases (supports_exists_neq_a_AB hid s g).1 hYes with ⟨d, hd⟩
    have : d ∈ relDom (associatedRelationAB M s) := by simpa [hDom]
    exact hd this

theorem relGraph_isFunction {D : Type*} (f : D → D) :
    RelIsFunctionAB (relGraph f) := by
  intro d e₁ e₂ h1 h2
  simpa [relGraph] using h1.trans h2.symm

theorem relGraph_isInjective {D : Type*} (f : D → D) (hf : Function.Injective f) :
    RelIsInjectiveAB (relGraph f) := by
  intro d₁ d₂ e h1 h2
  apply hf
  simpa [relGraph] using h1.symm.trans h2

theorem relDom_graph {D : Type*} (f : D → D) :
    relDom (relGraph f) = Set.univ := by
  ext d
  constructor
  · intro _
    simp
  · intro _
    refine ⟨f d, ?_⟩
    simp [relGraph]

theorem relRan_graph {D : Type*} (f : D → D) :
    relRan (relGraph f) = Set.range f := by
  ext e
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d, by simpa [relGraph] using hd.symm⟩
  · rintro ⟨d, rfl⟩
    exact ⟨d, by simp [relGraph]⟩

noncomputable def relationFunAB
    (R : Set (M.D × M.D)) (hfun : RelIsFunctionAB R) (hdom : relDom R = Set.univ) :
    M.D → M.D :=
  fun d => Classical.choose (show ∃ e, (d, e) ∈ R from by
    have hd : d ∈ relDom R := by simpa [hdom]
    exact hd)

theorem relationFun_spec_AB
    (R : Set (M.D × M.D)) (hfun : RelIsFunctionAB R) (hdom : relDom R = Set.univ) (d : M.D) :
    (d, relationFunAB (M := M) R hfun hdom d) ∈ R :=
  Classical.choose_spec (show ∃ e, (d, e) ∈ R from by
    have hd : d ∈ relDom R := by simpa [hdom]
    exact hd)

theorem relationFun_injective_AB
    (R : Set (M.D × M.D)) (hfun : RelIsFunctionAB R) (hinj : RelIsInjectiveAB R)
    (hdom : relDom R = Set.univ) :
    Function.Injective (relationFunAB (M := M) R hfun hdom) := by
  intro d₁ d₂ hEq
  apply hinj
  · exact relationFun_spec_AB (M := M) R hfun hdom d₁
  · simpa [hEq] using relationFun_spec_AB (M := M) R hfun hdom d₂

noncomputable def chosenWorldOfPairAB
    (s : Set M.W) (hfull : fullOnAB M s) (p : M.D × M.D) : M.W :=
  Classical.choose <|
    show ∃ w : M.W, w ∈ s ∧ associatedPairAB M w = p from by
      have hp : p ∈ associatedRelationAB M s := by
        rw [hfull]
        simp
      rcases hp with ⟨w, hw, hpair⟩
      exact ⟨w, hw, hpair⟩

theorem chosenWorldOfPairAB_spec
    (s : Set M.W) (hfull : fullOnAB M s) (p : M.D × M.D) :
    chosenWorldOfPairAB (M := M) s hfull p ∈ s ∧
      associatedPairAB M (chosenWorldOfPairAB (M := M) s hfull p) = p :=
  Classical.choose_spec <|
    show ∃ w : M.W, w ∈ s ∧ associatedPairAB M w = p from by
      have hp : p ∈ associatedRelationAB M s := by
        rw [hfull]
        simp
      rcases hp with ⟨w, hw, hpair⟩
      exact ⟨w, hw, hpair⟩

noncomputable def stateOfRelationAB
    (s : Set M.W) (hfull : fullOnAB M s) (R : Set (M.D × M.D)) : Set M.W :=
  { w | ∃ p, p ∈ R ∧ w = chosenWorldOfPairAB (M := M) s hfull p }

theorem stateOfRelationAB_subset
    (s : Set M.W) (hfull : fullOnAB M s) (R : Set (M.D × M.D)) :
    stateOfRelationAB (M := M) s hfull R ⊆ s := by
  intro w hw
  rcases hw with ⟨p, _, rfl⟩
  exact (chosenWorldOfPairAB_spec (M := M) s hfull p).1

theorem associatedRelation_stateOfRelationAB
    (s : Set M.W) (hfull : fullOnAB M s) (R : Set (M.D × M.D)) :
    associatedRelationAB M (stateOfRelationAB (M := M) s hfull R) = R := by
  ext p
  constructor
  · rintro ⟨w, hw, hwp⟩
    rcases hw with ⟨p', hp'R, rfl⟩
    have hpEq : p = p' := by
      simpa [chosenWorldOfPairAB_spec (M := M) s hfull p'] using hwp.symm
    simpa [hpEq] using hp'R
  · intro hp
    refine ⟨chosenWorldOfPairAB (M := M) s hfull p, ?_, ?_⟩
    · exact ⟨p, hp, rfl⟩
    · exact (chosenWorldOfPairAB_spec (M := M) s hfull p).2

theorem supports_etaAB_iff_finite
    (hfull : fullOnAB M s) (hid : M.isIdModel) (g : Assignment M.D) :
    supports M s g etaAB ↔ Finite M.D := by
  constructor
  · intro hEta
    by_contra hNotFinite
    letI : Infinite M.D := not_finite_iff_infinite.mp hNotFinite
    let f : M.D → M.D := infiniteEndomap M.D
    let t : Set M.W := stateOfRelationAB (M := M) s hfull (relGraph f)
    have htt : t ⊆ s := stateOfRelationAB_subset (M := M) s hfull (relGraph f)
    have hRel : associatedRelationAB M t = relGraph f :=
      associatedRelation_stateOfRelationAB (M := M) s hfull (relGraph f)
    have hAnte : supports M t g etaAntecedentAB := by
      refine ⟨?_, ?_⟩
      · exact (supports_dep_ab_AB hid t g).2 (by simpa [hRel] using relGraph_isFunction f)
      · refine ⟨?_, ?_⟩
        · exact (supports_dep_ba_AB hid t g).2 (by
            simpa [hRel] using relGraph_isInjective f (infiniteEndomap_injective M.D))
        · have hMissing : ∃ e : M.D, e ∉ Set.range f := by
            by_contra hNo
            apply infiniteEndomap_not_surjective M.D
            intro e
            by_contra he
            exact hNo ⟨e, he⟩
          rcases hMissing with ⟨e, he⟩
          exact (supports_exists_neq_b_AB hid t g).2 ⟨e, by simpa [hRel, relRan_graph] using he⟩
    have hNoCons : ¬ supports M t g (.inqExists 0 (neq (.var 0) termA)) := by
      rw [not_supports_exists_neq_a_AB hid t g]
      simpa [hRel, relDom_graph]
    exact hNoCons (hEta t htt hAnte)
  · intro hFinite
    intro t ht hAnte
    rcases hAnte with ⟨hFun, hRest⟩
    rcases hRest with ⟨hInj, hRan⟩
    have hRfun : RelIsFunctionAB (associatedRelationAB M t) := (supports_dep_ab_AB hid t g).1 hFun
    have hRinj : RelIsInjectiveAB (associatedRelationAB M t) := (supports_dep_ba_AB hid t g).1 hInj
    rcases (supports_exists_neq_b_AB hid t g).1 hRan with ⟨e, heMiss⟩
    by_cases hCons : supports M t g (.inqExists 0 (neq (.var 0) termA))
    · exact hCons
    · have hDom : relDom (associatedRelationAB M t) = Set.univ :=
        (not_supports_exists_neq_a_AB hid t g).1 hCons
      let f := relationFunAB (M := M) (associatedRelationAB M t) hRfun hDom
      have hfinj : Function.Injective f :=
        relationFun_injective_AB (M := M) (associatedRelationAB M t) hRfun hRinj hDom
      letI : Finite M.D := hFinite
      have hsurj : Function.Surjective f := Finite.surjective_of_injective hfinj
      rcases hsurj e with ⟨d, hde⟩
      exfalso
      apply heMiss
      refine ⟨d, ?_⟩
      rw [← hde]
      exact relationFun_spec_AB (M := M) (associatedRelationAB M t) hRfun hDom d

/-- The base-signature structure induced by a single world of an extended id-model. -/
def worldStructureOf (M : InfoModel (ABSignature sig)) (w : M.W) : ClassicalStructure sig where
  D := M.D
  hD := M.hD
  predInterp := fun P xs => M.predInterp w P xs
  rigidInterp := M.rigidInterp
  nonrigidInterp := fun f xs => M.nonrigidInterp w (Sum.inl f) xs

@[simp] theorem ClassicalStructure_denote_worldStructureOf
    (M : InfoModel (ABSignature sig)) (w : M.W) (g : Assignment M.D) :
    ∀ t : Term sig,
      ClassicalStructure.denote (worldStructureOf (sig := sig) M w) g t =
        denote M w g (embedTerm t)
  | .var x => rfl
  | .rigidApp f args => by
      have hArgs :
          (fun i => ClassicalStructure.denote (worldStructureOf (sig := sig) M w) g (args i)) =
            (fun i => denote M w g (embedTerm (args i))) := by
        funext i
        exact ClassicalStructure_denote_worldStructureOf M w g (args i)
      simpa [ClassicalStructure.denote, denote, worldStructureOf, ABSignature.embedTerm] using
        congrArg (M.rigidInterp f) hArgs
  | .nonrigidApp f args => by
      have hArgs :
          (fun i => ClassicalStructure.denote (worldStructureOf (sig := sig) M w) g (args i)) =
            (fun i => denote M w g (embedTerm (args i))) := by
        funext i
        exact ClassicalStructure_denote_worldStructureOf M w g (args i)
      simpa [ClassicalStructure.denote, denote, worldStructureOf, ABSignature.embedTerm] using
        congrArg (M.nonrigidInterp w (Sum.inl f)) hArgs

theorem classicalSatisfies_worldStructureOf_iff
    (M : InfoModel (ABSignature sig)) (hid : M.isIdModel) (w : M.W) (g : Assignment M.D) :
    ∀ φ : Formula sig,
      ClassicalStructure.satisfies (worldStructureOf (sig := sig) M w) g φ ↔
        worldSatisfies M w g (embedFormula φ)
  | .pred P ts => by
      have hArgs :
          (fun i => ClassicalStructure.denote (worldStructureOf (sig := sig) M w) g (ts i)) =
            (fun i => denote M w g (embedTerm (ts i))) := by
        funext i
        exact ClassicalStructure_denote_worldStructureOf M w g (ts i)
      constructor
      · intro h
        change M.predInterp w P (fun i =>
          ClassicalStructure.denote (worldStructureOf (sig := sig) M w) g (ts i)) at h
        change M.predInterp w P (fun i => denote M w g (embedTerm (ts i)))
        have hPred :
            M.predInterp w P (fun i =>
              ClassicalStructure.denote (worldStructureOf (sig := sig) M w) g (ts i)) =
              M.predInterp w P (fun i => denote M w g (embedTerm (ts i))) :=
          congrArg (M.predInterp w P) hArgs
        exact hPred ▸ h
      · intro h
        change M.predInterp w P (fun i =>
          ClassicalStructure.denote (worldStructureOf (sig := sig) M w) g (ts i))
        change M.predInterp w P (fun i => denote M w g (embedTerm (ts i))) at h
        have hPred :
            M.predInterp w P (fun i =>
              ClassicalStructure.denote (worldStructureOf (sig := sig) M w) g (ts i)) =
              M.predInterp w P (fun i => denote M w g (embedTerm (ts i))) :=
          congrArg (M.predInterp w P) hArgs
        exact hPred.symm ▸ h
  | .eq t u => by
      constructor
      · intro hEq
        have hEq' :
            ClassicalStructure.denote (worldStructureOf (sig := sig) M w) g t =
              ClassicalStructure.denote (worldStructureOf (sig := sig) M w) g u := by
          simpa [ClassicalStructure.satisfies] using hEq
        exact (hid w _ _).2 (by
          simpa [ClassicalStructure_denote_worldStructureOf, ABSignature.embedFormula] using hEq')
      · intro hEq
        have hEq' :
            ClassicalStructure.denote (worldStructureOf (sig := sig) M w) g t =
              ClassicalStructure.denote (worldStructureOf (sig := sig) M w) g u := by
          exact (hid w _ _).1 (by
            simpa [ClassicalStructure_denote_worldStructureOf, ABSignature.embedFormula] using hEq)
        simpa [ClassicalStructure.satisfies] using hEq'
  | .bot => by
      simp [ClassicalStructure.satisfies, worldSatisfies, ABSignature.embedFormula]
  | .conj φ ψ => by
      simp [ClassicalStructure.satisfies, worldSatisfies, ABSignature.embedFormula,
        classicalSatisfies_worldStructureOf_iff M hid w g φ,
        classicalSatisfies_worldStructureOf_iff M hid w g ψ]
  | .inqDisj φ ψ => by
      simp [ClassicalStructure.satisfies, worldSatisfies, ABSignature.embedFormula,
        classicalSatisfies_worldStructureOf_iff M hid w g φ,
        classicalSatisfies_worldStructureOf_iff M hid w g ψ]
  | .imp φ ψ => by
      simp [ClassicalStructure.satisfies, worldSatisfies, ABSignature.embedFormula,
        classicalSatisfies_worldStructureOf_iff M hid w g φ,
        classicalSatisfies_worldStructureOf_iff M hid w g ψ]
  | .forall_ x φ => by
      constructor
      · intro h d
        exact (classicalSatisfies_worldStructureOf_iff M hid w (Assignment.update g x d) φ).1 (h d)
      · intro h d
        exact (classicalSatisfies_worldStructureOf_iff M hid w (Assignment.update g x d) φ).2 (h d)
  | .inqExists x φ => by
      constructor
      · rintro ⟨d, hd⟩
        exact ⟨d, (classicalSatisfies_worldStructureOf_iff M hid w (Assignment.update g x d) φ).1 hd⟩
      · rintro ⟨d, hd⟩
        exact ⟨d, (classicalSatisfies_worldStructureOf_iff M hid w (Assignment.update g x d) φ).2 hd⟩

/-- The generalized canonical full id-model built from a classical structure. -/
def generalizedCanonicalFullIdModel (S : ClassicalStructure sig) : InfoModel (ABSignature sig) where
  W := S.D × S.D
  D := S.D
  hW := by
    rcases S.hD with ⟨d⟩
    exact ⟨(d, d)⟩
  hD := S.hD
  predInterp := fun _ P xs => S.predInterp P xs
  rigidInterp := S.rigidInterp
  nonrigidInterp := fun w f xs =>
    match f with
    | Sum.inl f' => S.nonrigidInterp f' xs
    | Sum.inr ABConst.a => w.1
    | Sum.inr ABConst.b => w.2
  localEq := fun _ x y => x = y
  localEq_equiv := by
    intro _
    exact ⟨fun x => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
  localEq_congr_pred := by
    intro _ P xs ys hxy
    have hEq : xs = ys := funext hxy
    simp [hEq]
  localEq_congr_rigid := by
    intro _ f xs ys hxy
    have hEq : xs = ys := funext hxy
    simp [hEq]
  localEq_congr_nonrigid := by
    intro w f xs ys hxy
    cases f with
    | inl f' =>
        have hEq : xs = ys := funext hxy
        simp [hEq]
    | inr ab =>
        cases ab
        · rfl
        · rfl

theorem generalizedCanonicalFullIdModel_isIdModel (S : ClassicalStructure sig) :
    (generalizedCanonicalFullIdModel S).isIdModel := by
  intro w d e
  rfl

theorem generalizedCanonicalFullIdModel_full (S : ClassicalStructure sig) :
    fullOnAB (generalizedCanonicalFullIdModel S) Set.univ := by
  unfold fullOnAB
  ext p
  constructor
  · intro _
    simp
  · intro _
    rcases p with ⟨d, e⟩
    refine ⟨(d, e), ?_, rfl⟩
    simp

theorem classical_support_in_canonical
    (S : ClassicalStructure sig) (g : Assignment S.D) {φ : Formula sig}
    (hClass : Formula.isClassical φ) :
    supports (generalizedCanonicalFullIdModel S) Set.univ g (embedFormula φ) ↔
      ClassicalStructure.satisfies S g φ := by
  constructor
  · intro hSupp
    have hWorld :
        ∀ w, worldSatisfies (generalizedCanonicalFullIdModel S) w g (embedFormula φ) := by
      intro w
      exact
        (classical_support_iff_worldwise
          (M := generalizedCanonicalFullIdModel S)
          (g := g)
          (φ := embedFormula φ)
          (ABSignature.embedFormula_isClassical hClass)).1 hSupp w (by simp)
    rcases S.hD with ⟨d⟩
    exact
      (classicalSatisfies_worldStructureOf_iff
        (M := generalizedCanonicalFullIdModel S)
        (generalizedCanonicalFullIdModel_isIdModel S)
        (d, d)
        g
        φ).2 (hWorld (d, d))
  · intro hSat
    apply
      (classical_support_iff_worldwise
        (M := generalizedCanonicalFullIdModel S)
        (g := g)
        (φ := embedFormula φ)
        (ABSignature.embedFormula_isClassical hClass)).2
    intro w _
    exact
      (classicalSatisfies_worldStructureOf_iff
        (M := generalizedCanonicalFullIdModel S)
        (generalizedCanonicalFullIdModel_isIdModel S)
        w
        g
        φ).1 hSat

/-- Finite first-order validity on the classical surface represented by `Formula sig`. -/
def finiteFOLValid (φ : Formula sig) : Prop :=
  ∀ (S : ClassicalStructure sig) [Finite S.D] (g : Assignment S.D),
    ClassicalStructure.satisfies S g φ

theorem finite_validity_reduction
    {α : Formula sig} (hClass : Formula.isClassical α) :
    finiteFOLValid α ↔
      idValid (sig := ABSignature sig)
        (.imp etaAB (.inqDisj (embedFormula α) thetaAB)) := by
  constructor
  · intro hFinite M hid s g hEmpty
    intro t ht hEta
    by_cases hTheta : supports M t g thetaAB
    · exact Or.inr hTheta
    · by_cases hts : t = ∅
      · subst hts
        exact Or.inl (supports_empty M g (embedFormula α))
      · have hFull : fullOnAB M t := by
          by_contra hNotFull
          exact hTheta ((supports_thetaAB_iff_nonfull (M := M) hid t g).2 hNotFull)
        have hFin : Finite M.D := (supports_etaAB_iff_finite (M := M) (s := t) hFull hid g).1 hEta
        have hWorld : ∀ w, w ∈ t → worldSatisfies M w g (embedFormula α) := by
          intro w hw
          let S := worldStructureOf (sig := sig) M w
          letI : Finite S.D := hFin
          have hSat : ClassicalStructure.satisfies S g α := hFinite S g
          exact
            (classicalSatisfies_worldStructureOf_iff
              (M := M)
              hid
              w
              g
              α).1 hSat
        exact Or.inl <|
          (classical_support_iff_worldwise
            (M := M)
            (g := g)
            (φ := embedFormula α)
            (ABSignature.embedFormula_isClassical hClass)).2 hWorld
  · intro hId S _ g
    let M := generalizedCanonicalFullIdModel S
    have hEta : globallySupports M g etaAB := by
      exact
        (supports_etaAB_iff_finite
          (M := M)
          (s := Set.univ)
          (generalizedCanonicalFullIdModel_full S)
          (generalizedCanonicalFullIdModel_isIdModel S)
          g).2 (show Finite S.D from inferInstance)
    have hDisj :
        globallySupports M g (.inqDisj (embedFormula α) thetaAB) := by
      have hImp :
          globallySupports M g (.imp etaAB (.inqDisj (embedFormula α) thetaAB)) := by
        exact hId M (generalizedCanonicalFullIdModel_isIdModel S) Set.univ g (by
          intro φ hφ
          cases hφ)
      exact hImp Set.univ (Subset.rfl) hEta
    have hNotTheta : ¬ globallySupports M g thetaAB := by
      intro hTheta
      have hFalse : ¬ fullOnAB M Set.univ :=
        (supports_thetaAB_iff_nonfull
          (M := M)
          (generalizedCanonicalFullIdModel_isIdModel S)
          Set.univ
          g).1 hTheta
      exact hFalse (generalizedCanonicalFullIdModel_full S)
    have hAlpha :
        globallySupports M g (embedFormula α) := by
      rcases hDisj with hα | hθ
      · exact hα
      · exact False.elim (hNotTheta hθ)
    exact (classical_support_in_canonical (sig := sig) S g hClass).1 hAlpha

end GenericAB

end InqBQ
end HeytingLean
