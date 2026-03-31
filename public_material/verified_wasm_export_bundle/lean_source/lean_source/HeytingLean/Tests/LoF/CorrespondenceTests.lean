import Mathlib.Tactic
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Closed
import Mathlib.CategoryTheory.Category.Preorder
import HeytingLean.LoF.Combinators.Topos.StepsSite
import HeytingLean.LoF.Combinators.Category.BranchialSpan
import HeytingLean.LoF.Combinators.Category.BranchialBicategory
import HeytingLean.LoF.Combinators.Category.BranchialBicategoryTrunc
import HeytingLean.LoF.Combinators.Topos.Truncation
import HeytingLean.LoF.Combinators.Topos.ClosureVsTruncation
import HeytingLean.LoF.Combinators.Topos.DenseTopologyLoFOps
import HeytingLean.LoF.Correspondence.LoFSKY
import HeytingLean.LoF.Correspondence.LoFPrimaryClosedSKYBool
import HeytingLean.LoF.Correspondence.LoFPrimarySKYBool
import HeytingLean.LoF.MRSystems.StablePropositions

/-!
# CorrespondenceTests — computed and structural checks (SKY / LoF / (M,R))

This is a small but *nontrivial* test suite that goes beyond compile-only smoke checks:

- Branchial ancestor quotient is exactly isomorphism in the thin reachability category.
- Branchial common-ancestor data can be packaged as an actual span in the bicategory of spans in `Type`.
- Both LoF↦SKY naming conventions are supported (repo vs spec-table).
- Closed LoFPrimary expressions translate to SKY Church booleans and reduce to canonical truth values.
- (M,R) stable propositions form a Heyting algebra and match stable predicates on selectors.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open CategoryTheory
open HeytingLean.LoF
open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category
open HeytingLean.LoF.Correspondence

/-! ## A. Branchial: ancestor equivalence ↔ thin isomorphism -/

example (t : Comb) :
    let s := BranchialSpan.refl t
    BranchialSpan.AncestorEqv s s ↔ Nonempty (s.ancestor ≅ s.ancestor) := by
  intro s
  simpa using (BranchialSpan.AncestorEqv.iff_nonempty_iso (s₁ := s) (s₂ := s))

/-! ## A'. Branchial spans as actual spans (in `Type`) -/

open Combinators.Category.Branchial

-- The canonical common-ancestor span exists as a genuine 1-morphism in the bicategory of spans in `Type`.
#check Branchial.lCommonSpan

-- Witness-style `BranchialSpan` is equivalent to a point of the canonical span apex.
example (t u : Comb) : BranchialSpan t u ≃ (Branchial.lCommonSpan t u).apex :=
  BranchialSpan.equivCommonApex t u

/-! ## A''. Branchial spans with truncated ancestors (path-insensitive) -/

-- A path-insensitive common-ancestor span also exists (truncating the path component).
#check Branchial.lCommonSpanTrunc

/-! ## A'''. SKY multiway: computed edges + a depth-1 branchial witness -/

namespace SKYComputed

open HeytingLean.LoF.Comb
open HeytingLean.LoF.Combinators.Category

abbrev t0 : Comb :=
  (Comb.app (Comb.app .K .K) (Comb.app (Comb.app .K .K) .S))

def edRoot : Comb.EventData := { rule := .K, path := [] }
def childRoot : Comb := .K

def edRight : Comb.EventData := { rule := .K, path := [Comb.Dir.R] }
def childRight : Comb := Comb.app (Comb.app .K .K) .K

-- The multiway enumerator deterministically lists both possible one-step edges from `t0`.
lemma stepEdgesList_t0_eq :
    Comb.stepEdgesList t0 = [(edRoot, childRoot), (edRight, childRight)] := by
  native_decide

-- Turning those edges into labeled one-step morphisms gives a depth-1 branchial witness
-- between the two distinct children.
lemma branchialAt_t0_children : BranchialAt 1 childRoot childRight := by
  refine ⟨t0, ?_, ?_⟩
  · refine ⟨
      LSteps.trans
        { ed := edRoot
          mem := by native_decide }
        (.refl childRoot),
      by simp [LSteps.length]⟩
  · refine ⟨
      LSteps.trans
        { ed := edRight
          mem := by native_decide }
        (.refl childRight),
      by simp [LSteps.length]⟩

end SKYComputed

/-! ## B. LoF↦SKY: both naming conventions -/

open LoFTerm

-- Repo convention: `mark ↦ S`, `unmark ↦ K`, `reentry ↦ Y`.
example : LoFTerm.toSKY .mark = (.S : Comb) := rfl
example : LoFTerm.toSKY .unmark = (.K : Comb) := rfl
example : LoFTerm.toSKY .reentry = (.Y : Comb) := rfl

-- Spec-table convention: `mark ↦ K`, `unmark ↦ S`, `reentry ↦ Y`.
example : LoFTerm.toSKY_spec .mark = (.K : Comb) := rfl
example : LoFTerm.toSKY_spec .unmark = (.S : Comb) := rfl
example : LoFTerm.toSKY_spec .reentry = (.Y : Comb) := rfl

-- A concrete “spec naming” one-step reduction: `mark x y ↦ x` maps to the SKY `K`-rule.
example (x y : LoFTerm) :
    Comb.Step
        (LoFTerm.toSKY_spec (LoFTerm.app (LoFTerm.app .mark x) y))
        (LoFTerm.toSKY_spec x) := by
  have h : LoFStepSpec.Step (LoFTerm.app (LoFTerm.app .mark x) y) x := by
    -- Unfold: `StepSpec t u` is `LoFStep.Step (swap t) (swap u)`.
    -- Here `swap (mark x y) = unmark (swap x) (swap y)`, so this is `unmark_rule`.
    change LoFStep.Step
        (LoFTerm.swapMarkUnmark (LoFTerm.app (LoFTerm.app .mark x) y))
        (LoFTerm.swapMarkUnmark x)
    simpa [LoFTerm.swapMarkUnmark] using
      (LoFStep.Step.unmark_rule (LoFTerm.swapMarkUnmark x) (LoFTerm.swapMarkUnmark y))
  exact LoFStepSpec.step_toSKY_spec h

/-! ## B'. Closed LoFPrimary ↦ SKY Church booleans -/

open HeytingLean.LoF.Correspondence.LoFPrimaryClosed

def closedExample : HeytingLean.LoF.LoFPrimary.Expr 0 :=
  -- `¬False ∨ False` = `True`.
  HeytingLean.LoF.LoFPrimary.Expr.juxt
    (HeytingLean.LoF.LoFPrimary.Expr.mark HeytingLean.LoF.LoFPrimary.Expr.void)
    HeytingLean.LoF.LoFPrimary.Expr.void

#check toSKYBool_correct closedExample

/-! ## B''. LoFPrimary (with variables) ↦ SKY Church booleans (via environments) -/

open HeytingLean.LoF.Correspondence.LoFPrimarySKYBool

namespace EnvBridge

def rhoTrue : Fin 1 → Bool := fun _ => true
def rhoFalse : Fin 1 → Bool := fun _ => false

def openExample : HeytingLean.LoF.LoFPrimary.Expr 1 :=
  -- x ∨ ¬x  (always true)
  HeytingLean.LoF.LoFPrimary.Expr.juxt
    (HeytingLean.LoF.LoFPrimary.Expr.var 0)
    (HeytingLean.LoF.LoFPrimary.Expr.mark (HeytingLean.LoF.LoFPrimary.Expr.var 0))

#check LoFPrimarySKYBool.toSKYBool_correct openExample rhoTrue
#check LoFPrimarySKYBool.toSKYBool_correct openExample rhoFalse

end EnvBridge

/-! ## B'''. LoFPrimary: computed semantics via truth sets -/

open HeytingLean.LoF.LoFPrimary

-- `closedExample` is logically `True`, so with 0 variables its truth-set has exactly one valuation.
lemma trueSet_closedExample_card : (LoFPrimary.trueSet closedExample).card = 1 := by
  native_decide

-- `openExample` is `x ∨ ¬x`, so its truth-set contains both valuations on one variable.
lemma trueSet_openExample_card : (LoFPrimary.trueSet EnvBridge.openExample).card = 2 := by
  native_decide

/-! ## C. (M,R): stable propositions and stable predicates -/

namespace MRToy

open HeytingLean.ClosingTheLoop.MR
open HeytingLean.LoF.MRSystems

def toyH : Set (Unit → Bool) := Set.univ

def toySystem : MRSystem where
  A := Unit
  B := Bool
  H := toyH
  f := fun _ => true
  hf := by simp [toyH]
  Sel := Set.univ
  Φf := fun _ => ⟨fun _ => true, by simp [toyH]⟩
  hΦf := by simp

def mapTrue : AdmissibleMap toySystem :=
  ⟨fun _ => true, by simp [toySystem, toyH]⟩

def mapFalse : AdmissibleMap toySystem :=
  ⟨fun _ => false, by simp [toySystem, toyH]⟩

def toySelector : Selector toySystem :=
  ⟨fun b =>
      match b with
      | true => mapFalse
      | false => mapTrue,
    by simp [toySystem]⟩

def toyRI (b : toySystem.B) : RightInverseAt toySystem b where
  β := fun g => ⟨fun _ => g, by simp [toySystem]⟩
  right_inv := by
    intro g
    rfl

abbrev RI : RightInverseAt toySystem true := toyRI true

-- Stable propositions (predicates on closed selectors) have a Heyting algebra structure.
example : HeytingAlgebra (StableProp (S := toySystem) (b := true) RI) := by
  infer_instance

-- A nontrivial stable proposition on closed selectors: “the closed selector picks `mapTrue` at `true`”.
def Q : StableProp (S := toySystem) (b := true) RI :=
  fun Φc => Φc.1 true = mapTrue

-- Extending then restricting is the identity on stable propositions.
example : StablePred.restrict (S := toySystem) (b := true) RI (StablePred.extend (S := toySystem) (b := true) RI Q) = Q := by
  simp

-- Restricting then extending is the identity on stable predicates.
example (P : StablePred (S := toySystem) (b := true) RI) :
    StablePred.extend (S := toySystem) (b := true) RI (StablePred.restrict (S := toySystem) (b := true) RI P) = P := by
  simp

end MRToy

/-! ## D. Topos truncation: a concrete dense-closure quotient example -/

namespace DenseClosureExample

open CategoryTheory
open HeytingLean.LoF.Combinators.Topos

inductive Two | bot | top deriving DecidableEq, Repr

namespace Two

instance : Preorder Two where
  le a b :=
    match a, b with
    | bot, _ => True
    | top, top => True
    | top, bot => False
  le_refl a := by
    cases a <;> simp
  le_trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;> simp at *

lemma bot_le (a : Two) : Two.bot ≤ a := by
  cases a <;> simp [Two.instPreorder]

end Two

abbrev C := Two

noncomputable def J : GrothendieckTopology C := GrothendieckTopology.dense

noncomputable def Sbot : Sieve Two.top :=
  Sieve.ofObjects (fun (_ : Unit) => Two.bot) Two.top

lemma close_Sbot_eq_top : (J.close Sbot) = (⊤ : Sieve Two.top) := by
  ext Y f
  constructor
  · intro _
    trivial
  · intro _
    change (Sbot.pullback f) ∈ (GrothendieckTopology.dense : GrothendieckTopology C) Y
    intro Y' g
    refine ⟨Two.bot, CategoryTheory.homOfLE (Two.bot_le Y'), ?_⟩
    change Sbot ((CategoryTheory.homOfLE (Two.bot_le Y')) ≫ g ≫ f)
    refine ⟨(), ?_⟩
    exact ⟨𝟙 Two.bot⟩

-- In the closure quotient, the proper sieve `Sbot` becomes equal to `⊤`.
example :
    (Quot.mk _ Sbot : CloseQuot (C := C) (J := J) Two.top) =
      Quot.mk _ (⊤ : Sieve Two.top) := by
  apply Quot.sound
  change J.close Sbot = J.close (⊤ : Sieve Two.top)
  have h1 : J.close Sbot = (⊤ : Sieve Two.top) := close_Sbot_eq_top
  have h2 : J.close (⊤ : Sieve Two.top) = (⊤ : Sieve Two.top) := by
    have : (⊤ : Sieve Two.top) ∈ J Two.top := J.top_mem Two.top
    exact (J.close_eq_top_iff_mem (S := (⊤ : Sieve Two.top))).2 this
  simp [h1, h2]

end DenseClosureExample

/-! ## D'. Dense topology: operation compatibility on closed sieves (G.2) -/

-- These are the precise Lean-level “ops match” statements used to discharge the (formerly scoped) G.2 item:
-- for the dense Grothendieck topology, closed sieves are the double-negation (Boolean) core, and the
-- Heyting operations on `ClosedSieve` agree with the ambient sieve operations under coercion.
#check HeytingLean.LoF.Combinators.Topos.DenseTopology.closedSieveEquivClassicalCore
#check HeytingLean.LoF.Combinators.Topos.DenseTopology.coe_bot
#check HeytingLean.LoF.Combinators.Topos.DenseTopology.coe_himp
#check HeytingLean.LoF.Combinators.Topos.DenseTopology.coe_sup
#check HeytingLean.LoF.Combinators.Topos.DenseTopology.coe_compl

/-! ## D''. Dense topology: a finite preorder with nontrivial closed sieves (G.1 extra) -/

namespace DenseNontrivialClosedSievesExample

open CategoryTheory
open HeytingLean.LoF.Combinators.Topos

inductive V3 | a | b | top deriving DecidableEq, Repr

namespace V3

def le : V3 → V3 → Prop
  | a, a => True
  | b, b => True
  | top, top => True
  | a, top => True
  | b, top => True
  | _, _ => False

instance : Preorder V3 where
  le := le
  le_refl x := by
    cases x <;> simp [le]
  le_trans x y z hxy hyz := by
    cases x <;> cases y <;> cases z <;> simp [le] at *

lemma a_le_top : V3.a ≤ V3.top := by
  simp [LE.le, le]

lemma b_le_top : V3.b ≤ V3.top := by
  simp [LE.le, le]

end V3

abbrev C := V3

noncomputable def Sa : Sieve V3.top :=
  Sieve.ofObjects (fun (_ : Unit) => V3.a) V3.top

noncomputable def Sb : Sieve V3.top :=
  Sieve.ofObjects (fun (_ : Unit) => V3.b) V3.top

lemma Sa_of_a (f : V3.a ⟶ V3.top) : Sa f := by
  refine ⟨(), ?_⟩
  exact ⟨𝟙 V3.a⟩

lemma Sb_of_b (f : V3.b ⟶ V3.top) : Sb f := by
  refine ⟨(), ?_⟩
  exact ⟨𝟙 V3.b⟩

lemma Sa_iff (Y : C) (f : Y ⟶ V3.top) : Sa f ↔ Y = V3.a := by
  constructor
  · intro h
    rcases h with ⟨_, ⟨g⟩⟩
    have : Y ≤ V3.a := CategoryTheory.leOfHom g
    cases Y <;> simp [LE.le, V3.le] at this
    · rfl
  · intro hY
    subst hY
    exact Sa_of_a f

lemma Sb_iff (Y : C) (f : Y ⟶ V3.top) : Sb f ↔ Y = V3.b := by
  constructor
  · intro h
    rcases h with ⟨_, ⟨g⟩⟩
    have : Y ≤ V3.b := CategoryTheory.leOfHom g
    cases Y <;> simp [LE.le, V3.le] at this
    · rfl
  · intro hY
    subst hY
    exact Sb_of_b f

lemma Sa_compl_apply_iff (Y : C) (f : Y ⟶ V3.top) : (Sa : Sieve V3.top)ᶜ f ↔ Sb f := by
  classical
  cases Y with
  | a =>
      have hSbFalse : ¬ Sb f := by
        intro hSb
        have : (V3.a : C) = V3.b := (Sb_iff (Y := V3.a) (f := f)).1 hSb
        cases this
      constructor
      · intro h
        have : ¬ Sa ((𝟙 (V3.a : C)) ≫ f) :=
          (DenseTopology.compl_apply_iff (S := Sa) (f := f)).1 h _ (𝟙 _)
        have : False := this (by simpa using Sa_of_a f)
        exact False.elim this
      · intro h
        exact False.elim (hSbFalse h)
  | b =>
      constructor
      · intro _
        exact Sb_of_b f
      · intro _
        refine (DenseTopology.compl_apply_iff (S := Sa) (f := f)).2 ?_
        intro Z g
        have hZ : Z = (V3.b : C) := by
          have : Z ≤ (V3.b : C) := CategoryTheory.leOfHom g
          cases Z <;> simp [LE.le, V3.le] at this
          · rfl
        subst hZ
        have : ¬ Sa (g ≫ f) := by
          intro hSa
          have : (V3.b : C) = V3.a := (Sa_iff (Y := V3.b) (f := g ≫ f)).1 hSa
          cases this
        exact this
  | top =>
      have hSbFalse : ¬ Sb f := by
        intro hSb
        have : (V3.top : C) = V3.b := (Sb_iff (Y := V3.top) (f := f)).1 hSb
        cases this
      constructor
      · intro h
        have ga : (V3.a : C) ⟶ (V3.top : C) := CategoryTheory.homOfLE (V3.a_le_top)
        have : ¬ Sa (ga ≫ f) := (DenseTopology.compl_apply_iff (S := Sa) (f := f)).1 h _ ga
        have : False := this (Sa_of_a (ga ≫ f))
        exact False.elim this
      · intro h
        exact False.elim (hSbFalse h)

lemma Sa_compl_eq_Sb : (Sa : Sieve V3.top)ᶜ = Sb := by
  classical
  ext Y f
  simp [Sa_compl_apply_iff (Y := Y) (f := f)]

lemma Sb_compl_eq_Sa : (Sb : Sieve V3.top)ᶜ = Sa := by
  classical
  ext Y f
  cases Y with
  | a =>
      constructor
      · intro _
        exact Sa_of_a f
      · intro _
        refine (DenseTopology.compl_apply_iff (S := Sb) (f := f)).2 ?_
        intro Z g
        have hZ : Z = (V3.a : C) := by
          have : Z ≤ (V3.a : C) := CategoryTheory.leOfHom g
          cases Z <;> simp [LE.le, V3.le] at this
          · rfl
        subst hZ
        have : ¬ Sb (g ≫ f) := by
          intro hSb
          have : (V3.a : C) = V3.b := (Sb_iff (Y := V3.a) (f := g ≫ f)).1 hSb
          cases this
        exact this
  | b =>
      have hSaFalse : ¬ Sa f := by
        intro hSa
        have : (V3.b : C) = V3.a := (Sa_iff (Y := V3.b) (f := f)).1 hSa
        cases this
      constructor
      · intro h
        have : ¬ Sb ((𝟙 (V3.b : C)) ≫ f) :=
          (DenseTopology.compl_apply_iff (S := Sb) (f := f)).1 h _ (𝟙 _)
        have : False := this (by simpa using Sb_of_b f)
        exact False.elim this
      · intro h
        exact False.elim (hSaFalse h)
  | top =>
      have hSaFalse : ¬ Sa f := by
        intro hSa
        have : (V3.top : C) = V3.a := (Sa_iff (Y := V3.top) (f := f)).1 hSa
        cases this
      constructor
      · intro h
        have gb : (V3.b : C) ⟶ (V3.top : C) := CategoryTheory.homOfLE (V3.b_le_top)
        have : ¬ Sb (gb ≫ f) := (DenseTopology.compl_apply_iff (S := Sb) (f := f)).1 h _ gb
        have : False := this (Sb_of_b (gb ≫ f))
        exact False.elim this
      · intro h
        exact False.elim (hSaFalse h)

lemma Sa_doubleNeg_eq : (Sa : Sieve V3.top)ᶜᶜ = Sa := by
  classical
  simp [Sa_compl_eq_Sb, Sb_compl_eq_Sa]

lemma Sb_doubleNeg_eq : (Sb : Sieve V3.top)ᶜᶜ = Sb := by
  classical
  simp [Sa_compl_eq_Sb, Sb_compl_eq_Sa]

noncomputable def SaClosed :
    ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) V3.top := by
  classical
  refine ⟨Sa, ?_⟩
  refine ⟨Sa, ?_⟩
  simp [DenseTopology.close_eq_doubleNeg (C := C) (S := Sa), Sa_doubleNeg_eq]

noncomputable def SbClosed :
    ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) V3.top := by
  classical
  refine ⟨Sb, ?_⟩
  refine ⟨Sb, ?_⟩
  simp [DenseTopology.close_eq_doubleNeg (C := C) (S := Sb), Sb_doubleNeg_eq]

lemma SaClosed_ne_SbClosed : SaClosed ≠ SbClosed := by
  intro h
  have hS :
      ((SaClosed :
            ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) V3.top) :
          Sieve V3.top) =
        ((SbClosed :
            ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) V3.top) :
          Sieve V3.top) :=
    congrArg
      (fun (S : ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) V3.top) =>
        (S : Sieve V3.top))
      h
  have ha : (SaClosed : Sieve V3.top) (CategoryTheory.homOfLE (V3.a_le_top)) :=
    Sa_of_a _
  have hb : (SbClosed : Sieve V3.top) (CategoryTheory.homOfLE (V3.a_le_top)) := by
    simpa [hS] using ha
  have : (V3.a : C) = V3.b :=
    (Sb_iff (Y := V3.a) (f := CategoryTheory.homOfLE (V3.a_le_top))).1 hb
  cases this

-- Closed-sieve join regularizes `Sa ⊔ Sb` to `⊤` in the dense topology.
example :
    ((SaClosed ⊔ SbClosed :
          ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) V3.top) :
        Sieve V3.top) =
      (⊤ : Sieve V3.top) := by
  have hcoe :
      ((SaClosed ⊔ SbClosed :
            ClosedSieve (C := C) (GrothendieckTopology.dense : GrothendieckTopology C) V3.top) :
          Sieve V3.top) =
        ((Sa : Sieve V3.top) ⊔ (Sb : Sieve V3.top))ᶜᶜ :=
    DenseTopology.coe_sup (C := C) (X := V3.top) SaClosed SbClosed

  have hcompl : ((Sa : Sieve V3.top) ⊔ (Sb : Sieve V3.top))ᶜ = (⊥ : Sieve V3.top) := by
    classical
    ext Y f
    cases Y with
    | a =>
        constructor
        · intro h
          have : ¬ (Sa ⊔ Sb : Sieve V3.top) ((𝟙 (V3.a : C)) ≫ f) :=
            (DenseTopology.compl_apply_iff (S := (Sa ⊔ Sb : Sieve V3.top)) (f := f)).1 h _ (𝟙 _)
          have : False := this (Or.inl (Sa_of_a f))
          exact False.elim this
        · intro h
          cases h
    | b =>
        constructor
        · intro h
          have : ¬ (Sa ⊔ Sb : Sieve V3.top) ((𝟙 (V3.b : C)) ≫ f) :=
            (DenseTopology.compl_apply_iff (S := (Sa ⊔ Sb : Sieve V3.top)) (f := f)).1 h _ (𝟙 _)
          have : False := this (Or.inr (Sb_of_b f))
          exact False.elim this
        · intro h
          cases h
    | top =>
        constructor
        · intro h
          have ga : (V3.a : C) ⟶ (V3.top : C) := CategoryTheory.homOfLE (V3.a_le_top)
          have : ¬ (Sa ⊔ Sb : Sieve V3.top) (ga ≫ f) :=
            (DenseTopology.compl_apply_iff (S := (Sa ⊔ Sb : Sieve V3.top)) (f := f)).1 h _ ga
          have : False := this (Or.inl (Sa_of_a (ga ≫ f)))
          exact False.elim this
        · intro h
          cases h

  have hnn : ((Sa : Sieve V3.top) ⊔ (Sb : Sieve V3.top))ᶜᶜ = (⊤ : Sieve V3.top) := by
    simp [hcompl]

  have :
      ((Saᶜ ⊓ Sbᶜ : Sieve V3.top)ᶜ) = (⊤ : Sieve V3.top) := by
    simpa [compl_sup] using hnn

  simpa [hcoe, compl_sup] using this

end DenseNontrivialClosedSievesExample

/-! ## E. SKY reachability site: a nontrivial dense-closure quotient example on `StepsCat` -/

namespace StepsDenseClosureExample

open CategoryTheory
open HeytingLean.LoF.Combinators.Topos

abbrev C : Type := StepsCat
noncomputable def J : GrothendieckTopology C := stepsDenseTopology

/-!
Key trick: every term `t` has a strict predecessor `(K t) K` that reduces in one step to `t`.

This yields, for any target `X`, a **covering sieve** whose generators are the arrows
`(K g) K ⟶ X` for each `g ⟶ X`. The sieve is typically **proper** but its `dense`-closure is `⊤`.
-/

def kwrap (t : C) : C :=
  Comb.app (Comb.app .K t) .K

lemma kwrap_steps (t : C) : Comb.Steps (kwrap t) t := by
  refine Comb.Steps.trans (t := kwrap t) (u := t) (v := t) ?_ (Comb.Steps.refl t)
  simpa [kwrap] using Comb.Step.K_rule (x := t) (y := (.K : Comb))

abbrev Index (X : C) : Type := Σ g : C, g ⟶ X

noncomputable def genObj {X : C} (i : Index X) : C :=
  kwrap i.1

noncomputable def genArr {X : C} (i : Index X) : genObj (X := X) i ⟶ X :=
  CategoryTheory.homOfLE (kwrap_steps i.1) ≫ i.2

noncomputable def kWrapSieve (X : C) : Sieve X :=
  Sieve.ofArrows (Y := fun i : Index X => genObj (X := X) i) (f := fun i => genArr (X := X) i)

lemma kWrapSieve_mem_dense (X : C) :
    kWrapSieve X ∈ (GrothendieckTopology.dense : GrothendieckTopology C) X := by
  intro Yobj f
  refine ⟨kwrap Yobj, CategoryTheory.homOfLE (kwrap_steps Yobj), ?_⟩
  -- Conclude membership in the sieve using `ofArrows_mk`.
  simpa [kWrapSieve, genArr, genObj] using
    (Sieve.ofArrows_mk (Y := fun i : Index X => genObj (X := X) i) (f := fun i => genArr (X := X) i)
      (i := (⟨Yobj, f⟩ : Index X)))

lemma close_kWrapSieve_eq_top (X : C) :
    (J.close (kWrapSieve X)) = (⊤ : Sieve X) := by
  -- `stepsDenseTopology` is definitionally `GrothendieckTopology.dense`.
  dsimp [J, stepsDenseTopology]
  -- `close S = ⊤ ↔ S ∈ J`.
  apply
    (GrothendieckTopology.close_eq_top_iff_mem
        (J₁ := (GrothendieckTopology.dense : GrothendieckTopology C)) (S := kWrapSieve X)).2
  exact kWrapSieve_mem_dense (X := X)

-- Hence `¬¬(kWrapSieve X) = ⊤` (dense closure is double negation).
lemma kWrapSieve_doubleNeg_eq_top (X : C) :
    (kWrapSieve X : Sieve X)ᶜᶜ = (⊤ : Sieve X) := by
  have hclose :
      (GrothendieckTopology.dense : GrothendieckTopology C).close (kWrapSieve X) =
        (⊤ : Sieve X) := by
    simpa [J, stepsDenseTopology] using close_kWrapSieve_eq_top (X := X)
  simpa [HeytingLean.LoF.Combinators.Topos.DenseTopology.close_eq_doubleNeg (C := C)
    (S := (kWrapSieve X : Sieve X))] using hclose

-- Therefore the pseudocomplement of `kWrapSieve X` is `⊥` (since `¬¬S = ⊤` forces `¬S = ⊥`).
lemma kWrapSieve_compl_eq_bot (X : C) :
    (kWrapSieve X : Sieve X)ᶜ = (⊥ : Sieve X) := by
  have hnn : (kWrapSieve X : Sieve X)ᶜᶜ = (⊤ : Sieve X) := kWrapSieve_doubleNeg_eq_top (X := X)
  have : (kWrapSieve X : Sieve X)ᶜᶜᶜ = (⊤ : Sieve X)ᶜ := by
    simpa using congrArg (fun (T : Sieve X) => Tᶜ) hnn
  simpa using this

-- Concrete instance: on the SKY reachability site, we get a *proper* sieve whose closure is `⊤`.
lemma kWrapSieve_K_ne_top : kWrapSieve (.K : C) ≠ (⊤ : Sieve (.K : C)) := by
  intro hTop
  have hId : kWrapSieve (.K : C) (𝟙 (.K : C)) := by
    simp [hTop]
  -- Unpack membership in the `ofArrows` presentation.
  rcases
      (Sieve.mem_ofArrows_iff (Y := fun i : Index (.K : C) => genObj (X := (.K : C)) i)
            (f := fun i => genArr (X := (.K : C)) i) (g := 𝟙 (.K : C))).1 hId with
    ⟨i, a, ha⟩
  -- But `K` is normal, so any multi-step from `K` is equality; contradiction since `genObj i` is an application.
  have hSteps : Comb.Steps (.K : Comb) (genObj (X := (.K : C)) i) := CategoryTheory.leOfHom a
  have hEq : (genObj (X := (.K : C)) i) = (.K : Comb) := by
    -- `K` cannot take a step; hence the only `Steps` target is itself.
    have hN : Comb.Normal (.K : Comb) := Comb.K_normal
    -- Induction on `Steps` starting at a normal term.
    have : ∀ {u : Comb}, Comb.Steps (.K : Comb) u → u = (.K : Comb) := by
      intro u hu
      cases hu with
      | refl _ => rfl
      | trans hstep _ =>
          exfalso
          exact (hN _ hstep)
    exact this hSteps
  -- `genObj i` is definitionally an application, so it cannot equal `K`.
  cases i with
  | mk g hg =>
      dsimp [genObj, kwrap] at hEq
      cases hEq

-- Therefore `kWrapSieve K` is a proper sieve whose dense-closure is `⊤`.
example : (J.close (kWrapSieve (.K : C))) = (⊤ : Sieve (.K : C)) :=
  close_kWrapSieve_eq_top (X := (.K : C))

-- And its pseudocomplement is `⊥`.
example : (kWrapSieve (.K : C) : Sieve (.K : C))ᶜ = (⊥ : Sieve (.K : C)) :=
  kWrapSieve_compl_eq_bot (X := (.K : C))

-- Sanity: for the dense topology, closure is double negation on the Heyting algebra of sieves.
example (X : C) (S : Sieve X) :
    (GrothendieckTopology.dense : GrothendieckTopology C).close S = Sᶜᶜ := by
  simpa using
    (HeytingLean.LoF.Combinators.Topos.DenseTopology.close_eq_doubleNeg (C := C) (S := S))

end StepsDenseClosureExample

end LoF
end Tests
end HeytingLean
