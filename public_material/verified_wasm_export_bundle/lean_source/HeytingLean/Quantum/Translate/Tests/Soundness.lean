import HeytingLean.Quantum.Translate.RT
import HeytingLean.Quantum.OML.Sasaki
import HeytingLean.Quantum.Translate.Instances.BoolIdentity
import HeytingLean.Quantum.Translate.Laws

open HeytingLean.Quantum.Translate

section
variable {β α : Type _}
variable [HeytingLean.Quantum.OML.OrthocomplementedLattice β]
variable [HeytingLean.Quantum.OML.OrthomodularLattice β]
variable [Order.Frame α] [HeytingAlgebra α]

variable (F : QLMap β α)

example (x y : β) :
  F.toOmega (x ⊓ y) =
    Omega.inf (M := F.M) (F.toOmega x) (F.toOmega y) :=
  F.map_inf_toOmega x y

example (x y : β) :
  Omega.inf (M := F.M) (F.toOmega x)
              (Omega.imp (M := F.M) (F.toOmega x) (F.toOmega y))
  ≤ F.toOmega y :=
  F.mp x y

end

/-
Concrete complement-preserving example.

We equip `Prop` with the trivial modality `⊤` (sending everything to `True`) and
use the constant-`True` translation.  Under this modality every translation is
complement-preserving up to closure; we register the instance explicitly and
exercise the refined Sasaki bridge lemma.
-/

section TopConst
open HeytingLean.Quantum.OML

variable {β : Type _} [OrthocomplementedLattice β] [OrthomodularLattice β]

/-- Modality on `Prop` whose nucleus is the top element (constant `True`). -/
def topModality : Modality Prop :=
  { J := ⊤
    preserves_top := rfl }

/-- Constant-`True` translation into `Prop` equipped with `topModality`. -/
def TopConstQLMap : QLMap β Prop :=
{ M := topModality
  tr := fun _ => True
  map_inf := by intro _ _; rfl
  map_sup_le := by intro _ _; trivial }

/-- Complement preservation is trivial under the top modality. -/
def TopConstComplPreserving : QLMap.ComplPreserving (F := TopConstQLMap (β := β)) :=
  { compl_closed := by
      intro a
      -- Both sides reduce to `True` because the modality closes everything to `⊤`.
      simp [TopConstQLMap, topModality] }

example (a : β) : qPSR (TopConstQLMap (β := β)) a := by
  simp [qPSR, TopConstQLMap, topModality]

example (t a : β) : qDialectic (TopConstQLMap (β := β)) t a = True := by
  simp [qDialectic, TopConstQLMap, topModality]

/-- The refined Sasaki bridge specializes to the expected `True` bound for the
constant translation. -/
example (a b : β) :
    (TopConstQLMap (β := β)).tr (sasakiHook a b)
      ≤ (TopConstQLMap (β := β)).M.J
          (((TopConstQLMap (β := β)).tr a)ᶜ ⊔ (TopConstQLMap (β := β)).tr b) :=
by
  have h :=
    QLMap.sasakiHook_le_translated_nucleus_imp
      (F := TopConstQLMap (β := β))
      (hCompl := TopConstComplPreserving (β := β))
      (a := a) (b := b)
  -- Both sides are `True`, so the inequality holds by triviality.
  exact h

end TopConst

-- Propositional specialisations using the Boolean orthocomplemented instance.
section PropFacts
noncomputable section
open HeytingLean.Quantum.OML

-- Concrete orthocomplemented and orthomodular structure on `Prop`.
local instance : OrthocomplementedLattice Prop where
  compl := Not
  involutive := by intro a; by_cases h : a <;> simp [h]
  antitone := by
    intro a b h
    intro hb ha; exact hb (h ha)
  inf_compl := by intro a; by_cases h : a <;> simp [h]
  sup_compl := by intro a; by_cases h : a <;> simp [h]

@[simp] lemma prop_compl (p : Prop) : OrthocomplementedLattice.compl p = ¬ p := rfl

local instance : OrthomodularLattice Prop where
  orthomodular := by
    intro a b h
    apply propext
    constructor
    · intro hb
      by_cases ha : a
      · exact Or.inl ha
      · exact Or.inr ⟨ha, hb⟩
    · intro h'
      rcases h' with ha | hrest
      · exact h ha
      · exact hrest.2

example (p q : Prop) : p ∧ sasakiHook p q → q :=
by
  -- interpret lattice inequality as propositional implication
  have h := (sasaki_weak_mp (a := p) (b := q) : p ⊓ sasakiHook p q ≤ q)
  -- in `Prop`, `⊓` is `And`, so this is directly usable
  exact h

example (p q : Prop) : sasakiHook p q = (¬ p ∨ q) :=
by
  by_cases hp : p <;> simp [sasakiHook, hp]

end
end PropFacts

/-
Identity translation on `Prop` with the identity nucleus, exercising the refined
bridge in a concrete complement-preserving model.
-/
section PropIdentity
noncomputable section
open HeytingLean.Quantum.OML

local instance : OrthocomplementedLattice Prop where
  compl := Not
  involutive := by intro a; by_cases h : a <;> simp [h]
  antitone := by intro a b h hb ha; exact hb (h ha)
  inf_compl := by intro a; by_cases h : a <;> simp [h]
  sup_compl := by intro a; by_cases h : a <;> simp [h]

local instance : OrthomodularLattice Prop where
  orthomodular := by
    intro a b h
    apply propext
    constructor
    · intro hb
      by_cases ha : a
      · exact Or.inl ha
      · exact Or.inr ⟨ha, hb⟩
    · intro h'
      rcases h' with ha | hrest
      · exact h ha
      · exact hrest.2

def propIdModality : Modality Prop :=
  { J := ⊥
    preserves_top := rfl }

def propIdQLMap : QLMap Prop Prop :=
{ M := propIdModality
  tr := id
  map_inf := by intro _ _; rfl
  map_sup_le := by intro _ _; rfl }

instance : QLMap.ComplPreserving (F := propIdQLMap) :=
by
  refine ⟨?_⟩
  intro a
  rfl

example (p q : Prop) :
    propIdQLMap.tr (sasakiHook p q)
      ≤ propIdModality.J (((propIdQLMap.tr p)ᶜ) ⊔ propIdQLMap.tr q) := by
  simpa [propIdQLMap, propIdModality] using
    (QLMap.sasakiHook_le_translated_nucleus_imp
      (F := propIdQLMap) (hCompl := inferInstance) (a := p) (b := q))

end
end PropIdentity

/-
Identity translation on a non-Prop complete Boolean algebra (`Set ℕ`) with the identity modality.
-/
section SetIdentity
open HeytingLean.Quantum.Translate.Instances
open HeytingLean.Quantum.OML

example (p q : Set ℕ) :
    (boolIdentityQLMap (Set ℕ)).tr (sasakiHook p q)
      ≤ (boolIdentityQLMap (Set ℕ)).M.J
          (((boolIdentityQLMap (Set ℕ)).tr p)ᶜ ⊔ (boolIdentityQLMap (Set ℕ)).tr q) := by
  -- direct specialization of the refined bridge
  simpa using
    (QLMap.sasakiHook_le_translated_nucleus_imp
      (F := boolIdentityQLMap (Set ℕ)) (hCompl := inferInstance) (a := p) (b := q))

end SetIdentity
