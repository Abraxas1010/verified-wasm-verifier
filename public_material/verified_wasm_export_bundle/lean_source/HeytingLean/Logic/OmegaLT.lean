import HeytingLean.Logic.StageSemantics
import HeytingLean.LoF.Nucleus

/-
Ω-level Lawvere–Tierney (LT) scaffold and staged helpers.
Connects a lightweight `j : Ω → Ω` to derived connectives, and
adapts a `Reentry α` nucleus as an LT endomap on Ω.
-/

namespace HeytingLean
namespace Logic
namespace OmegaLT

open HeytingLean.Logic.Stage
open HeytingLean.LoF

universe u

/-- Minimal LT core: an endomap `j : Ω → Ω` to lift connectives. -/
structure LTCore (Ω : Type u) where
  j : Ω → Ω

namespace LTCore
variable {Ω : Type u}
variable [HeytingAlgebra Ω]

@[simp] def ltMeet (_L : LTCore Ω) (a b : Ω) : Ω := a ⊓ b
@[simp] def ltJoin (L : LTCore Ω) (a b : Ω) : Ω := L.j (a ⊔ b)
@[simp] def ltImp  (L : LTCore Ω) (a b : Ω) : Ω := L.j (a ⇨ b)
@[simp] def ltNeg  (L : LTCore Ω) (a : Ω)   : Ω := L.j (a ⇨ ⊥)

end LTCore

/-! ### Minimal LT laws and monotonicity lemmas -/

namespace LTCore
variable {Ω : Type u} [HeytingAlgebra Ω]

/-- Optional laws that make `j` behave like a closure and record
    basic Heyting monotonicities used by derived connectives. -/
structure Laws (L : LTCore Ω) : Prop where
  mono : Monotone L.j
  idem : ∀ a, L.j (L.j a) = L.j a
  ext  : ∀ a, a ≤ L.j a

variable (L : LTCore Ω)

lemma j_idem {h : Laws L} (a : Ω) : L.j (L.j a) = L.j a := h.idem a

/-- The LT join is monotone in its left argument. -/
lemma ltJoin_mono_left {h : Laws L} {a a' b : Ω}
    (ha : a ≤ a') : L.ltJoin a b ≤ L.ltJoin a' b := by
  unfold LTCore.ltJoin
  exact h.mono (sup_le_sup ha le_rfl)

/-- The LT join is monotone in its right argument. -/
lemma ltJoin_mono_right {h : Laws L} {a b b' : Ω}
    (hb : b ≤ b') : L.ltJoin a b ≤ L.ltJoin a b' := by
  unfold LTCore.ltJoin
  exact h.mono (sup_le_sup le_rfl hb)

/-- LT implication is monotone in its right argument under a monotone Heyting implication. -/
lemma ltImp_mono_right' {h : Laws L} (a : Ω)
    (himp : Monotone (fun b => a ⇨ b)) {b b' : Ω}
    (hb : b ≤ b') : L.ltImp a b ≤ L.ltImp a b' := by
  unfold LTCore.ltImp
  exact h.mono (himp hb)

/-- LT implication is antitone in its left argument under an antitone Heyting implication. -/
lemma ltImp_antitone_left' {h : Laws L} (b : Ω)
    (hanti : Antitone (fun a => a ⇨ b)) {a a' : Ω}
    (ha : a' ≤ a) : L.ltImp a b ≤ L.ltImp a' b := by
  unfold LTCore.ltImp
  exact h.mono (hanti ha)

end LTCore

/-! ### Staged transports across a bridge (placed under global `Logic.Stage`) -/

namespace Stage
end Stage

namespace HeytingLean.Logic.Stage

variable {α Ω : Type u} [LE α] [LE Ω] [HeytingAlgebra Ω]
open HeytingLean.Logic.OmegaLT

def Bridge.stageLTMeet (B : Bridge α Ω) (_L : LTCore Ω) (x y : α) : α :=
  B.lift ((B.shadow x) ⊓ (B.shadow y))

def Bridge.stageLTJoin (B : Bridge α Ω) (L : LTCore Ω) (x y : α) : α :=
  B.lift (L.ltJoin (B.shadow x) (B.shadow y))

def Bridge.stageLTImp (B : Bridge α Ω) (L : LTCore Ω) (x y : α) : α :=
  B.lift (L.ltImp (B.shadow x) (B.shadow y))

def Bridge.stageLTNeg (B : Bridge α Ω) (L : LTCore Ω) (x : α) : α :=
  B.lift (L.ltNeg (B.shadow x))

@[simp] theorem shadow_stageLTMeet (B : Bridge α Ω)
    (L : LTCore Ω) (x y : α) :
    B.shadow (B.stageLTMeet L x y) = B.shadow x ⊓ B.shadow y := by
  unfold Bridge.stageLTMeet; exact B.rt₁ _

@[simp] theorem shadow_stageLTJoin (B : Bridge α Ω)
    (L : LTCore Ω) (x y : α) :
    B.shadow (B.stageLTJoin L x y) = L.ltJoin (B.shadow x) (B.shadow y) := by
  unfold Bridge.stageLTJoin; exact B.rt₁ _

@[simp] theorem shadow_stageLTImp (B : Bridge α Ω)
    (L : LTCore Ω) (x y : α) :
    B.shadow (B.stageLTImp L x y) = L.ltImp (B.shadow x) (B.shadow y) := by
  unfold Bridge.stageLTImp; exact B.rt₁ _

@[simp] theorem shadow_stageLTNeg (B : Bridge α Ω)
    (L : LTCore Ω) (x : α) :
    B.shadow (B.stageLTNeg L x) = L.ltNeg (B.shadow x) := by
  unfold Bridge.stageLTNeg; exact B.rt₁ _

end HeytingLean.Logic.Stage

/-! ### Adapter: view a Reentry nucleus as an LT endomap on Ω -/

@[simp] def ofReentryOmega (α : Type u) [PrimaryAlgebra α]
    (R : Reentry α) : LTCore α :=
  { j := fun a => R a }

/-! ### Specialization on the fixed-point core `R.Omega` -/

namespace ReentryOmega
variable {α : Type u} [PrimaryAlgebra α]

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

/-- LT core on `R.Omega` where `j` is the identity (already fixed points). -/
@[simp] def ofFixed (R : Reentry α) : LTCore R.Omega := { j := id }

open HeytingLean.LoF

/-- Laws for the fixed LT core on `R.Omega` (including implication monotonicities). -/
theorem laws_ofFixed (R : Reentry α) :
    LTCore.Laws (ofFixed (α := α) R) := by
  refine ⟨?mono, ?idem, ?ext⟩
  · intro x y h; exact h
  · intro a; rfl
  · intro a; exact le_rfl

/-! Direct wrappers (no simp) for implication monotonicities on `R.Omega`. -/

/-- In the fixed Ω-core, implication remains monotone in its right argument. -/
theorem ltImp_mono_right_fixed
    (R : Reentry α) {a b b' : R.Omega} (hb : b ≤ b') :
    (ofFixed (α := α) R).ltImp a b ≤ (ofFixed (α := α) R).ltImp a b' := by
  -- `ltImp` is identity on implication under `ofFixed`.
  change (a ⇨ b) ≤ (a ⇨ b')
  have h₁ : (a ⊓ (a ⇨ b) : R.Omega) ≤ b :=
    HeytingLean.LoF.Reentry.inf_himp_le (R := R) (a := a) (b := b)
  have h₂ : ((a ⇨ b) ⊓ a : R.Omega) ≤ b := by
    have h_eq := inf_comm (a := (a ⇨ b)) (b := a) (α := R.Omega)
    exact (h_eq ▸ h₁)
  have h₃ : ((a ⇨ b) ⊓ a : R.Omega) ≤ b' := le_trans h₂ hb
  exact (HeytingLean.LoF.Reentry.inf_le_iff_le_himp (R := R)
    (a := (a ⇨ b)) (b := a) (c := b')).mp h₃

/-- In the fixed Ω-core, implication is antitone in its left argument. -/
theorem ltImp_antitone_left_fixed
    (R : Reentry α) {a a' b : R.Omega} (ha : a' ≤ a) :
    (ofFixed (α := α) R).ltImp a b ≤ (ofFixed (α := α) R).ltImp a' b := by
  -- `ltImp` is identity on implication under `ofFixed`.
  change (a ⇨ b) ≤ (a' ⇨ b)
  have h₁ : a' ⊓ (a ⇨ b) ≤ a ⊓ (a ⇨ b) :=
    inf_le_inf ha le_rfl
  have h₂ : (a ⊓ (a ⇨ b) : R.Omega) ≤ b :=
    HeytingLean.LoF.Reentry.inf_himp_le (R := R) (a := a) (b := b)
  have h₃ : (a' ⊓ (a ⇨ b) : R.Omega) ≤ b := le_trans h₁ h₂
  have h₄ : ((a ⇨ b) ⊓ a' : R.Omega) ≤ b := by
    have h_eq := inf_comm (a := (a ⇨ b)) (b := a') (α := R.Omega)
    exact (h_eq ▸ h₃)
  exact (HeytingLean.LoF.Reentry.inf_le_iff_le_himp (R := R)
    (a := (a ⇨ b)) (b := a') (c := b)).mp h₄

end ReentryOmega

end OmegaLT
end Logic
end HeytingLean
