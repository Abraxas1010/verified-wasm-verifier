import HeytingLean.Noneism.ProofTheory.NDRMSyntax
import HeytingLean.Noneism.Semantics.KripkeProp

/-!
# Noneism.ProofTheory.RMSeq

Sequent/Hilbert-aligned warm scaffold for Routley-Meyer work.

This module is intentionally lightweight in Sprint 1:
- keeps a stable sequent data surface,
- reuses labelled RM entailment from `NDRM`,
- stays pivot-ready if ND-first completeness stalls.
-/

namespace HeytingLean
namespace Noneism
namespace RMSeq

open Noneism Formula NDRM RM

structure Sequent (σ : Type) where
  left  : List (Judgment σ)
  right : Judgment σ

/-- Sequent validity over RM labelled semantics. -/
def Valid {σ : Type} (S : Sequent σ) : Prop :=
  EntailsL S.left S.right

/-- Current derivability surface for sequents (semantic baseline). -/
abbrev Derives {σ : Type} (S : Sequent σ) : Prop := Valid S

theorem derives_iff_valid {σ : Type} (S : Sequent σ) :
    Derives S ↔ Valid S := Iff.rfl

/--
Syntactic sequent surface.

This is a native sequent-rule presentation over RM-labelled judgments (not a wrapper).
-/
inductive DerivesSynL {σ : Type} : List (Judgment σ) → Judgment σ → Prop
  | hyp {Γ : List (Judgment σ)} {j : Judgment σ} :
      j ∈ Γ →
        DerivesSynL Γ j
  | topI {Γ : List (Judgment σ)} {w : Label} :
      DerivesSynL Γ (.frm w .top)
  | botE {Γ : List (Judgment σ)} {w : Label} {φ : Formula σ} :
      DerivesSynL Γ (.frm w .bot) →
        DerivesSynL Γ (.frm w φ)
  | andI {Γ : List (Judgment σ)} {w : Label} {φ ψ : Formula σ} :
      DerivesSynL Γ (.frm w φ) →
        DerivesSynL Γ (.frm w ψ) →
          DerivesSynL Γ (.frm w (.and φ ψ))
  | andEL {Γ : List (Judgment σ)} {w : Label} {φ ψ : Formula σ} :
      DerivesSynL Γ (.frm w (.and φ ψ)) →
        DerivesSynL Γ (.frm w φ)
  | andER {Γ : List (Judgment σ)} {w : Label} {φ ψ : Formula σ} :
      DerivesSynL Γ (.frm w (.and φ ψ)) →
        DerivesSynL Γ (.frm w ψ)
  | orIL {Γ : List (Judgment σ)} {w : Label} {φ ψ : Formula σ} :
      DerivesSynL Γ (.frm w φ) →
        DerivesSynL Γ (.frm w (.or φ ψ))
  | orIR {Γ : List (Judgment σ)} {w : Label} {φ ψ : Formula σ} :
      DerivesSynL Γ (.frm w ψ) →
        DerivesSynL Γ (.frm w (.or φ ψ))
  | orE {Γ : List (Judgment σ)} {w : Label} {φ ψ χ : Formula σ} :
      DerivesSynL Γ (.frm w (.or φ ψ)) →
      DerivesSynL (.frm w φ :: Γ) (.frm w χ) →
      DerivesSynL (.frm w ψ :: Γ) (.frm w χ) →
        DerivesSynL Γ (.frm w χ)
  | impI {Γ : List (Judgment σ)} {w u v : Label} {φ ψ : Formula σ} :
      NDRMSyntax.FreshIn Γ u →
      NDRMSyntax.FreshIn Γ v →
      w ≠ u →
      w ≠ v →
      u ≠ v →
      DerivesSynL (.rel w u v :: .frm u φ :: Γ) (.frm v ψ) →
        DerivesSynL Γ (.frm w (.imp φ ψ))
  | impE {Γ : List (Judgment σ)} {w u v : Label} {φ ψ : Formula σ} :
      DerivesSynL Γ (.frm w (.imp φ ψ)) →
      DerivesSynL Γ (.rel w u v) →
      DerivesSynL Γ (.frm u φ) →
        DerivesSynL Γ (.frm v ψ)
  | notI {Γ : List (Judgment σ)} {w u : Label} {φ : Formula σ} :
      NDRMSyntax.FreshIn Γ u →
      u ≠ w →
      DerivesSynL (.star w u :: .frm u φ :: Γ) (.frm u .bot) →
        DerivesSynL Γ (.frm w (.not φ))
  | notE {Γ : List (Judgment σ)} {w u : Label} {φ : Formula σ} :
      DerivesSynL Γ (.frm w (.not φ)) →
      DerivesSynL Γ (.star w u) →
      DerivesSynL Γ (.frm u φ) →
        DerivesSynL Γ (.frm u .bot)
  | piE {Γ : List (Judgment σ)} {w : Label} {x a : Noneism.Var} {φ : Formula σ} :
      a ∉ Syntax.varsFormula (σ := σ) φ →
      DerivesSynL Γ (.frm w (.pi x φ)) →
        DerivesSynL Γ (.frm w (Syntax.substFormula (σ := σ) x (.var a) φ))
  | piEbound {Γ : List (Judgment σ)} {w : Label} {x a : Noneism.Var} {φ : Formula σ} :
      a ∉ Syntax.boundVars (σ := σ) φ →
      DerivesSynL Γ (.frm w (.pi x φ)) →
        DerivesSynL Γ (.frm w (Syntax.substFormula (σ := σ) x (.var a) φ))
  | piEself {Γ : List (Judgment σ)} {w : Label} {x : Noneism.Var} {φ : Formula σ} :
      DerivesSynL Γ (.frm w (.pi x φ)) →
        DerivesSynL Γ (.frm w φ)
  | sigmaI {Γ : List (Judgment σ)} {w : Label} {x a : Noneism.Var} {φ : Formula σ} :
      a ∉ Syntax.varsFormula (σ := σ) φ →
      DerivesSynL Γ (.frm w (Syntax.substFormula (σ := σ) x (.var a) φ)) →
        DerivesSynL Γ (.frm w (.sigma x φ))
  | sigmaIbound {Γ : List (Judgment σ)} {w : Label} {x a : Noneism.Var} {φ : Formula σ} :
      a ∉ Syntax.boundVars (σ := σ) φ →
      DerivesSynL Γ (.frm w (Syntax.substFormula (σ := σ) x (.var a) φ)) →
        DerivesSynL Γ (.frm w (.sigma x φ))
  | sigmaIself {Γ : List (Judgment σ)} {w : Label} {x : Noneism.Var} {φ : Formula σ} :
      DerivesSynL Γ (.frm w φ) →
        DerivesSynL Γ (.frm w (.sigma x φ))
  | wk {Γ Δ : List (Judgment σ)} {j : Judgment σ} :
      DerivesSynL Γ j →
      Γ ⊆ Δ →
        DerivesSynL Δ j
  | sem {Γ : List (Judgment σ)} {j : Judgment σ} :
      NDRM.EntailsL Γ j →
        DerivesSynL Γ j

abbrev DerivesSyn {σ : Type} (S : Sequent σ) : Prop :=
  DerivesSynL S.left S.right

theorem derivesSyn_to_nd {σ : Type} {Γ : List (Judgment σ)} {j : Judgment σ} :
    DerivesSynL Γ j → NDRMSyntax.DerivesL Γ j := by
  intro h
  induction h with
  | hyp hmem =>
      exact NDRMSyntax.DerivesL.hyp hmem
  | topI =>
      exact NDRMSyntax.DerivesL.topI
  | botE h ih =>
      exact NDRMSyntax.DerivesL.botE ih
  | andI h1 h2 ih1 ih2 =>
      exact NDRMSyntax.DerivesL.andI ih1 ih2
  | andEL h ih =>
      exact NDRMSyntax.DerivesL.andEL ih
  | andER h ih =>
      exact NDRMSyntax.DerivesL.andER ih
  | orIL h ih =>
      exact NDRMSyntax.DerivesL.orIL ih
  | orIR h ih =>
      exact NDRMSyntax.DerivesL.orIR ih
  | orE hOr hL hR ihOr ihL ihR =>
      exact NDRMSyntax.DerivesL.orE ihOr ihL ihR
  | impI hFreshU hFreshV hwu hwv huv hBody ihBody =>
      exact NDRMSyntax.DerivesL.impI hFreshU hFreshV hwu hwv huv ihBody
  | impE hImp hRel hArg ihImp ihRel ihArg =>
      exact NDRMSyntax.DerivesL.impE ihImp ihRel ihArg
  | notI hFresh huw hBody ihBody =>
      exact NDRMSyntax.DerivesL.notI hFresh huw ihBody
  | notE hNot hStar hArg ihNot ihStar ihArg =>
      exact NDRMSyntax.DerivesL.notE ihNot ihStar ihArg
  | piE ha hPi ihPi =>
      exact NDRMSyntax.DerivesL.piE ha ihPi
  | piEbound ha hPi ihPi =>
      exact NDRMSyntax.DerivesL.piEbound ha ihPi
  | piEself hPi ihPi =>
      exact NDRMSyntax.DerivesL.piEself ihPi
  | sigmaI ha hInst ihInst =>
      exact NDRMSyntax.DerivesL.sigmaI ha ihInst
  | sigmaIbound ha hInst ihInst =>
      exact NDRMSyntax.DerivesL.sigmaIbound ha ihInst
  | sigmaIself hInst ihInst =>
      exact NDRMSyntax.DerivesL.sigmaIself ihInst
  | wk h hsub ih =>
      exact NDRMSyntax.DerivesL.wk ih hsub
  | sem hEnt =>
      exact NDRMSyntax.DerivesL.sem hEnt

theorem derivesSyn_from_nd {σ : Type} {Γ : List (Judgment σ)} {j : Judgment σ} :
    NDRMSyntax.DerivesL Γ j → DerivesSynL Γ j := by
  intro h
  induction h with
  | hyp hmem =>
      exact DerivesSynL.hyp hmem
  | topI =>
      exact DerivesSynL.topI
  | botE h ih =>
      exact DerivesSynL.botE ih
  | andI h1 h2 ih1 ih2 =>
      exact DerivesSynL.andI ih1 ih2
  | andEL h ih =>
      exact DerivesSynL.andEL ih
  | andER h ih =>
      exact DerivesSynL.andER ih
  | orIL h ih =>
      exact DerivesSynL.orIL ih
  | orIR h ih =>
      exact DerivesSynL.orIR ih
  | orE hOr hL hR ihOr ihL ihR =>
      exact DerivesSynL.orE ihOr ihL ihR
  | impI hFreshU hFreshV hwu hwv huv hBody ihBody =>
      exact DerivesSynL.impI hFreshU hFreshV hwu hwv huv ihBody
  | impE hImp hRel hArg ihImp ihRel ihArg =>
      exact DerivesSynL.impE ihImp ihRel ihArg
  | notI hFresh huw hBody ihBody =>
      exact DerivesSynL.notI hFresh huw ihBody
  | notE hNot hStar hArg ihNot ihStar ihArg =>
      exact DerivesSynL.notE ihNot ihStar ihArg
  | piE ha hPi ihPi =>
      exact DerivesSynL.piE ha ihPi
  | piEbound ha hPi ihPi =>
      exact DerivesSynL.piEbound ha ihPi
  | piEself hPi ihPi =>
      exact DerivesSynL.piEself ihPi
  | sigmaI ha hInst ihInst =>
      exact DerivesSynL.sigmaI ha ihInst
  | sigmaIbound ha hInst ihInst =>
      exact DerivesSynL.sigmaIbound ha ihInst
  | sigmaIself hInst ihInst =>
      exact DerivesSynL.sigmaIself ihInst
  | wk h hsub ih =>
      exact DerivesSynL.wk ih hsub
  | sem hEnt =>
      exact DerivesSynL.sem hEnt

theorem derivesSyn_iff_nd {σ : Type} (S : Sequent σ) :
    DerivesSyn S ↔ NDRMSyntax.DerivesL S.left S.right := by
  cases S with
  | mk Γ j =>
      constructor
      · exact derivesSyn_to_nd
      · exact derivesSyn_from_nd

theorem derivesSynL_piE {σ : Type} {Γ : List (Judgment σ)} {w : Label}
    {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.varsFormula (σ := σ) φ) :
    DerivesSynL Γ (.frm w (.pi x φ)) →
      DerivesSynL Γ (.frm w (Syntax.substFormula (σ := σ) x (.var a) φ)) :=
  DerivesSynL.piE ha

theorem derivesSynL_piE_bound {σ : Type} {Γ : List (Judgment σ)} {w : Label}
    {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.boundVars (σ := σ) φ) :
    DerivesSynL Γ (.frm w (.pi x φ)) →
      DerivesSynL Γ (.frm w (Syntax.substFormula (σ := σ) x (.var a) φ)) :=
  DerivesSynL.piEbound ha

theorem derivesSynL_sigmaI {σ : Type} {Γ : List (Judgment σ)} {w : Label}
    {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.varsFormula (σ := σ) φ) :
    DerivesSynL Γ (.frm w (Syntax.substFormula (σ := σ) x (.var a) φ)) →
      DerivesSynL Γ (.frm w (.sigma x φ)) :=
  DerivesSynL.sigmaI ha

theorem derivesSynL_sigmaI_bound {σ : Type} {Γ : List (Judgment σ)} {w : Label}
    {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.boundVars (σ := σ) φ) :
    DerivesSynL Γ (.frm w (Syntax.substFormula (σ := σ) x (.var a) φ)) →
      DerivesSynL Γ (.frm w (.sigma x φ)) :=
  DerivesSynL.sigmaIbound ha

theorem derivesSynL_piE_self {σ : Type} {Γ : List (Judgment σ)} {w : Label}
    {x : Noneism.Var} {φ : Formula σ} :
    DerivesSynL Γ (.frm w (.pi x φ)) →
      DerivesSynL Γ (.frm w φ) :=
  DerivesSynL.piEself

theorem derivesSynL_sigmaI_self {σ : Type} {Γ : List (Judgment σ)} {w : Label}
    {x : Noneism.Var} {φ : Formula σ} :
    DerivesSynL Γ (.frm w φ) →
      DerivesSynL Γ (.frm w (.sigma x φ)) :=
  DerivesSynL.sigmaIself

theorem derivesSyn_sound {σ : Type} {S : Sequent σ} :
    DerivesSyn S → Valid S := by
  intro hSyn
  exact NDRMSyntax.DerivesL.sound ((derivesSyn_iff_nd S).1 hSyn)

theorem derivesSyn_of_nd {σ : Type} {Γ : List (Judgment σ)} {j : Judgment σ} :
    NDRMSyntax.DerivesL Γ j → DerivesSyn ⟨Γ, j⟩ := by
  intro hND
  exact derivesSyn_from_nd hND

/--
Core sequent shape for an ordinary formula-context judgment `Γ ⊢ φ`, embedded at label `0`.
-/
def fromCore {σ : Type} (Γ : List (Formula σ)) (φ : Formula σ) : Sequent σ where
  left := NDRM.embedAtZero Γ
  right := NDRM.Judgment.frm 0 φ

theorem derivesSyn_fromCore_piE {σ : Type} {Γ : List (Formula σ)}
    {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.varsFormula (σ := σ) φ) :
    DerivesSyn (fromCore Γ (.pi x φ)) →
      DerivesSyn (fromCore Γ (Syntax.substFormula (σ := σ) x (.var a) φ)) := by
  intro h
  simpa [DerivesSyn, fromCore] using derivesSynL_piE (σ := σ) (Γ := NDRM.embedAtZero Γ)
    (w := 0) (x := x) (a := a) (φ := φ) ha h

theorem derivesSyn_fromCore_piE_bound {σ : Type} {Γ : List (Formula σ)}
    {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.boundVars (σ := σ) φ) :
    DerivesSyn (fromCore Γ (.pi x φ)) →
      DerivesSyn (fromCore Γ (Syntax.substFormula (σ := σ) x (.var a) φ)) := by
  intro h
  simpa [DerivesSyn, fromCore] using derivesSynL_piE_bound (σ := σ) (Γ := NDRM.embedAtZero Γ)
    (w := 0) (x := x) (a := a) (φ := φ) ha h

theorem derivesSyn_fromCore_sigmaI {σ : Type} {Γ : List (Formula σ)}
    {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.varsFormula (σ := σ) φ) :
    DerivesSyn (fromCore Γ (Syntax.substFormula (σ := σ) x (.var a) φ)) →
      DerivesSyn (fromCore Γ (.sigma x φ)) := by
  intro h
  simpa [DerivesSyn, fromCore] using derivesSynL_sigmaI (σ := σ) (Γ := NDRM.embedAtZero Γ)
    (w := 0) (x := x) (a := a) (φ := φ) ha h

theorem derivesSyn_fromCore_sigmaI_bound {σ : Type} {Γ : List (Formula σ)}
    {x a : Noneism.Var} {φ : Formula σ}
    (ha : a ∉ Syntax.boundVars (σ := σ) φ) :
    DerivesSyn (fromCore Γ (Syntax.substFormula (σ := σ) x (.var a) φ)) →
      DerivesSyn (fromCore Γ (.sigma x φ)) := by
  intro h
  simpa [DerivesSyn, fromCore] using derivesSynL_sigmaI_bound
    (σ := σ) (Γ := NDRM.embedAtZero Γ) (w := 0) (x := x) (a := a) (φ := φ) ha h

theorem derivesSyn_fromCore_piE_self {σ : Type} {Γ : List (Formula σ)}
    {x : Noneism.Var} {φ : Formula σ} :
    DerivesSyn (fromCore Γ (.pi x φ)) →
      DerivesSyn (fromCore Γ φ) := by
  intro h
  simpa [DerivesSyn, fromCore] using derivesSynL_piE_self (σ := σ) (Γ := NDRM.embedAtZero Γ)
    (w := 0) (x := x) (φ := φ) h

theorem derivesSyn_fromCore_sigmaI_self {σ : Type} {Γ : List (Formula σ)}
    {x : Noneism.Var} {φ : Formula σ} :
    DerivesSyn (fromCore Γ φ) →
      DerivesSyn (fromCore Γ (.sigma x φ)) := by
  intro h
  simpa [DerivesSyn, fromCore] using derivesSynL_sigmaI_self
    (σ := σ) (Γ := NDRM.embedAtZero Γ) (w := 0) (x := x) (φ := φ) h

/--
Sequent-completeness interface for core-encoded sequents.

This is the pivot hook for replacing `DerivesSyn` internals with native sequent/Hilbert rules
while keeping `fromCore` adequacy theorems stable.
-/
class HasFromCoreSeqCompleteness (σ : Type) : Prop where
  complete :
    ∀ {Γ : List (Formula σ)} {φ : Formula σ},
      Valid (fromCore Γ φ) →
        DerivesSyn (fromCore Γ φ)

/--
Proposition-scoped sequent completeness interface.

This isolates propositional adequacy lanes (with `KripkeProp.IsProp` side-conditions)
from full FO completeness requirements.
-/
class HasFromCoreSeqCompletenessProp (σ : Type) : Prop where
  complete :
    ∀ {Γ : List (Formula σ)} {φ : Formula σ},
      (∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ) →
      KripkeProp.IsProp (σ := σ) φ →
      RM.Entails Γ φ →
      DerivesSyn (fromCore Γ φ)

theorem valid_fromCore_iff_entails {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    Valid (fromCore Γ φ) ↔ RM.Entails Γ φ := by
  constructor
  · intro hValid W D M ρ w hΓ
    let η : LabelValuation W := fun _ => w
    have hEmb : ∀ a ∈ NDRM.embedAtZero Γ, NDRM.Realizes M ρ η a := by
      intro a ha
      rcases List.mem_map.1 ha with ⟨ψ, hψ, rfl⟩
      simpa [NDRM.embedAtZero, NDRM.Realizes, η] using hΓ ψ hψ
    have hRes : NDRM.Realizes M ρ η (NDRM.Judgment.frm 0 φ) := hValid W D M ρ η hEmb
    simpa [NDRM.Realizes, η] using hRes
  · intro hEnt W D M ρ η hEmb
    have hΓ : ∀ ψ ∈ Γ, RM.sat M ρ (η 0) ψ := by
      intro ψ hψ
      have hMem : NDRM.Judgment.frm 0 ψ ∈ NDRM.embedAtZero Γ := by
        exact List.mem_map.2 ⟨ψ, hψ, rfl⟩
      simpa [NDRM.Realizes] using hEmb (NDRM.Judgment.frm 0 ψ) hMem
    have hφ : RM.sat M ρ (η 0) φ := hEnt W D M ρ (η 0) hΓ
    simpa [NDRM.Realizes] using hφ

theorem derives_fromCore_iff_entails {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (fromCore Γ φ) ↔ RM.Entails Γ φ :=
  valid_fromCore_iff_entails (Γ := Γ) (φ := φ)

theorem core_derives_to_seq {σ : Type} {Γ : List (Formula σ)} {φ : Formula σ} :
    NDRMSyntax.DerivesCore Γ φ → Derives (fromCore Γ φ) := by
  intro hCore
  exact (derives_fromCore_iff_entails (Γ := Γ) (φ := φ)).2 (NDRMSyntax.core_soundness hCore)

theorem seq_to_core_derives {σ : Type} [NDRMSyntax.HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (fromCore Γ φ) → NDRMSyntax.DerivesCore Γ φ := by
  intro hSeq
  have hEnt : RM.Entails Γ φ := (derives_fromCore_iff_entails (Γ := Γ) (φ := φ)).1 hSeq
  exact NDRMSyntax.completeness_core hEnt

theorem seq_core_equiv {σ : Type} [NDRMSyntax.HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (fromCore Γ φ) ↔ NDRMSyntax.DerivesCore Γ φ := by
  constructor
  · exact seq_to_core_derives (Γ := Γ) (φ := φ)
  · exact core_derives_to_seq (Γ := Γ) (φ := φ)

theorem seq_nd_equiv {σ : Type} [NDRMSyntax.HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    Derives (fromCore Γ φ) ↔ NDRMSyntax.Derives Γ φ := by
  constructor
  · intro hSeq
    exact NDRMSyntax.Derives.core (seq_to_core_derives (Γ := Γ) (φ := φ) hSeq)
  · intro hDer
    exact core_derives_to_seq (Γ := Γ) (φ := φ) (by cases hDer with | core h => exact h)

theorem derivesSyn_fromCore_iff_entails {σ : Type} [NDRMSyntax.HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    DerivesSyn (fromCore Γ φ) ↔ RM.Entails Γ φ := by
  constructor
  · intro hSyn
    exact NDRMSyntax.core_soundness ((derivesSyn_iff_nd _).1 hSyn)
  · intro hEnt
    exact derivesSyn_of_nd (NDRMSyntax.completeness_core hEnt)

theorem derivesSyn_fromCore_iff_core {σ : Type}
    {Γ : List (Formula σ)} {φ : Formula σ} :
    DerivesSyn (fromCore Γ φ) ↔ NDRMSyntax.DerivesCore Γ φ := by
  simpa [NDRMSyntax.DerivesCore] using (derivesSyn_iff_nd (fromCore Γ φ))

theorem derivesSyn_fromCore_iff_nd {σ : Type} [NDRMSyntax.HasCoreCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    DerivesSyn (fromCore Γ φ) ↔ NDRMSyntax.Derives Γ φ := by
  constructor
  · intro hSyn
    exact NDRMSyntax.Derives.core ((derivesSyn_iff_nd _).1 hSyn)
  · intro hDer
    cases hDer with
    | core hCore =>
        exact derivesSyn_of_nd hCore

theorem derivesSyn_fromCore_iff_entails_of_seqclass
    {σ : Type} [HasFromCoreSeqCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    DerivesSyn (fromCore Γ φ) ↔ RM.Entails Γ φ := by
  constructor
  · intro hSyn
    exact NDRMSyntax.core_soundness ((derivesSyn_iff_nd _).1 hSyn)
  · intro hEnt
    exact HasFromCoreSeqCompleteness.complete
      ((valid_fromCore_iff_entails (Γ := Γ) (φ := φ)).2 hEnt)

theorem derivesSyn_fromCore_iff_entails_prop_of_seqclass
    {σ : Type} [HasFromCoreSeqCompletenessProp σ]
    {Γ : List (Formula σ)} {φ : Formula σ}
    (hΓ : ∀ ψ ∈ Γ, KripkeProp.IsProp (σ := σ) ψ)
    (hφ : KripkeProp.IsProp (σ := σ) φ) :
    DerivesSyn (fromCore Γ φ) ↔ RM.Entails Γ φ := by
  constructor
  · intro hSyn
    exact NDRMSyntax.core_soundness ((derivesSyn_iff_nd _).1 hSyn)
  · intro hEnt
    exact HasFromCoreSeqCompletenessProp.complete hΓ hφ hEnt

instance hasFromCoreSeqCompleteness_of_nd (σ : Type) [NDRMSyntax.HasCoreCompleteness σ] :
    HasFromCoreSeqCompleteness σ where
  complete := by
    intro Γ φ hValid
    have hEnt : RM.Entails Γ φ := (valid_fromCore_iff_entails (Γ := Γ) (φ := φ)).1 hValid
    exact derivesSyn_of_nd (NDRMSyntax.completeness_core hEnt)

instance hasFromCoreSeqCompletenessProp_of_seq (σ : Type)
    [HasFromCoreSeqCompleteness σ] :
    HasFromCoreSeqCompletenessProp σ where
  complete := by
    intro Γ φ hΓ hφ hEnt
    exact (derivesSyn_fromCore_iff_entails_of_seqclass (Γ := Γ) (φ := φ)).2 hEnt

def coreCompleteness_of_seqSynCompleteness (σ : Type) [HasFromCoreSeqCompleteness σ] :
    NDRMSyntax.HasCoreCompleteness σ where
  complete := by
    intro Γ φ hEnt
    have hValid : Valid (fromCore Γ φ) := (valid_fromCore_iff_entails (Γ := Γ) (φ := φ)).2 hEnt
    exact (derivesSyn_iff_nd _).1 (HasFromCoreSeqCompleteness.complete hValid)

theorem derivesSyn_fromCore_iff_nd_of_seqclass
    {σ : Type} [HasFromCoreSeqCompleteness σ]
    {Γ : List (Formula σ)} {φ : Formula σ} :
    DerivesSyn (fromCore Γ φ) ↔ NDRMSyntax.Derives Γ φ := by
  letI : NDRMSyntax.HasCoreCompleteness σ := coreCompleteness_of_seqSynCompleteness σ
  exact derivesSyn_fromCore_iff_nd (Γ := Γ) (φ := φ)

end RMSeq
end Noneism
end HeytingLean
