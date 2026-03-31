import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Nucleus
import Mathlib.Tactic.DeriveFintype
import HeytingLean.LoF.PrimaryAlgebra
import HeytingLean.LoF.Nucleus

/-!
# Computable Test Kit for Lens Verification

## Foundational Distinction: Witness vs Chooser

- **Heyting Algebra = Witness**: To assert P, construct evidence of P.
- **Boolean Algebra = Witness + Chooser**: Oracle decides `P ∨ ¬P` without evidence.

For Diamond:
- Heyting layer (lattice ops) is constructive - pattern matching on 4 elements
- Complete lattice requires chooser for `Set` membership via `Classical.dec`
-/

namespace HeytingLean
namespace Tests
namespace Bridges
namespace ComputableTestKit

open HeytingLean.LoF

/-! ## Four-Element Diamond Lattice -/

/-- The four-element diamond lattice: bot < left, right < top with left ⊓ right = bot -/
inductive Diamond
  | bot
  | left
  | right
  | top
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace Diamond

/-! ### Computable Operations -/

def le' : Diamond → Diamond → Bool
  | .bot, _ => true
  | .left, .left => true
  | .left, .top => true
  | .right, .right => true
  | .right, .top => true
  | .top, .top => true
  | _, _ => false

def inf' : Diamond → Diamond → Diamond
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, x => x
  | x, .top => x
  | .left, .left => .left
  | .right, .right => .right
  | .left, .right => .bot
  | .right, .left => .bot

def sup' : Diamond → Diamond → Diamond
  | .top, _ => .top
  | _, .top => .top
  | .bot, x => x
  | x, .bot => x
  | .left, .left => .left
  | .right, .right => .right
  | .left, .right => .top
  | .right, .left => .top

def himp' : Diamond → Diamond → Diamond
  | .bot, _ => .top
  | .top, x => x
  | .left, .bot => .right
  | .left, .left => .top
  | .left, .right => .right
  | .left, .top => .top
  | .right, .bot => .left
  | .right, .left => .left
  | .right, .right => .top
  | .right, .top => .top

def compl' : Diamond → Diamond
  | .bot => .top
  | .left => .right
  | .right => .left
  | .top => .bot

/-! ### Export Helpers -/

def all : List Diamond := [.bot, .left, .right, .top]

def toInt : Diamond → Int
  | .bot => 0
  | .left => 1
  | .right => 2
  | .top => 3

/-! ### Basic Instances -/

instance : LE Diamond where le x y := le' x y = true
instance : LT Diamond where lt x y := x ≤ y ∧ ¬y ≤ x
instance : Top Diamond where top := .top
instance : Bot Diamond where bot := .bot
instance : Max Diamond where max := sup'
instance : Min Diamond where min := inf'
instance : HImp Diamond where himp := himp'
instance : HasCompl Diamond where compl := compl'

instance : DecidableRel (α := Diamond) (· ≤ ·) := fun x y =>
  if h : le' x y = true then isTrue h else isFalse h

instance : DecidableRel (α := Diamond) (· < ·) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Order Structure - Following Mathlib Bool pattern: direct `by decide` -/

instance : Preorder Diamond where
  le_refl := by decide
  le_trans := by decide

instance : PartialOrder Diamond where
  le_antisymm := by decide

instance : SemilatticeInf Diamond where
  inf := inf'
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

instance : SemilatticeSup Diamond where
  sup := sup'
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

instance instLattice : Lattice Diamond where
  inf := inf'
  sup := sup'
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

instance : OrderTop Diamond where
  le_top := by decide

instance : OrderBot Diamond where
  bot_le := by decide

instance : BoundedOrder Diamond where
  top := .top
  bot := .bot
  le_top := by decide
  bot_le := by decide

instance : DistribLattice Diamond where
  le_sup_inf := by decide

instance : GeneralizedHeytingAlgebra Diamond where
  himp := himp'
  le_himp_iff := by decide

instance instHeytingAlgebra : HeytingAlgebra Diamond where
  himp := himp'
  le_himp_iff := by decide
  himp_bot := by decide

/-! ### Complete Lattice (Classical) -/

open Classical in
noncomputable def sSup' (s : Set Diamond) : Diamond :=
  if .top ∈ s then .top
  else if .left ∈ s ∧ .right ∈ s then .top
  else if .left ∈ s then .left
  else if .right ∈ s then .right
  else .bot

open Classical in
noncomputable def sInf' (s : Set Diamond) : Diamond :=
  if .bot ∈ s then .bot
  else if .left ∈ s ∧ .right ∈ s then .bot
  else if .left ∈ s then .left
  else if .right ∈ s then .right
  else .top

noncomputable instance instSupSet : SupSet Diamond where sSup := sSup'
noncomputable instance instInfSet : InfSet Diamond where sInf := sInf'

open Classical in
noncomputable instance : CompleteSemilatticeSup Diamond where
  le_sSup := by
    intro s x hx
    simp only [SupSet.sSup, sSup']
    split_ifs with h1 h2 h3 h4
    · exact le_top
    · exact le_top
    · cases x <;> simp_all [LE.le, le']
    · cases x <;> simp_all [LE.le, le']
    · cases x <;> simp_all [LE.le, le']
  sSup_le := by
    intro s x h
    simp only [SupSet.sSup, sSup']
    split_ifs with h1 h2 h3 h4
    · exact h .top h1
    · obtain ⟨hl, hr⟩ := h2
      have hl' := h .left hl
      have hr' := h .right hr
      cases x <;> simp_all [LE.le, le']
    · exact h .left h3
    · exact h .right h4
    · exact bot_le

open Classical in
noncomputable instance : CompleteSemilatticeInf Diamond where
  sInf_le := by
    intro s x hx
    simp only [InfSet.sInf, sInf']
    split_ifs with h1 h2 h3 h4
    · exact bot_le
    · exact bot_le
    · cases x <;> simp_all [LE.le, le']
    · cases x <;> simp_all [LE.le, le']
    · cases x <;> simp_all [LE.le, le']
  le_sInf := by
    intro s x h
    simp only [InfSet.sInf, sInf']
    split_ifs with h1 h2 h3 h4
    · exact h .bot h1
    · obtain ⟨hl, hr⟩ := h2
      have hl' := h .left hl
      have hr' := h .right hr
      cases x <;> simp_all [LE.le, le']
    · exact h .left h3
    · exact h .right h4
    · exact le_top

noncomputable instance instCompleteLattice : CompleteLattice Diamond where
  __ := instLattice
  __ := instSupSet
  __ := instInfSet
  le_sSup := CompleteSemilatticeSup.le_sSup
  sSup_le := CompleteSemilatticeSup.sSup_le
  sInf_le := CompleteSemilatticeInf.sInf_le
  le_sInf := CompleteSemilatticeInf.le_sInf
  le_top := fun _ => le_top
  bot_le := fun _ => bot_le

/-! ### Frame Instance -/

open Classical in
noncomputable instance instFrame : Order.Frame Diamond where
  __ := instCompleteLattice
  __ := instHeytingAlgebra

noncomputable instance : PrimaryAlgebra Diamond where

/-! ## Nucleus and Reentry -/

def idClose : Diamond → Diamond := id

theorem idClose_idempotent (x : Diamond) : idClose (idClose x) = idClose x := rfl
theorem idClose_map_inf (x y : Diamond) : idClose (x ⊓ y) = idClose x ⊓ idClose y := rfl
theorem idClose_le_apply (x : Diamond) : x ≤ idClose x := le_refl x

/-- Discrete nucleus on Diamond - uses the Frame's SemilatticeInf -/
noncomputable def discreteNucleus : @Nucleus Diamond instCompleteLattice.toSemilatticeInf where
  toFun := idClose
  map_inf' := by intro x y; rfl
  idempotent' := by intro x; rfl
  le_apply' := by intro x; exact le_refl x

/-- Reentry for Diamond with discrete topology.
    Support is restricted to .left so that primordial_minimal holds:
    the only nontrivial fixed point x ≤ left is left itself. -/
noncomputable def discreteReentry : Reentry Diamond where
  nucleus := discreteNucleus
  primordial := .left
  counter := .right
  support := .left  -- Restricted support makes primordial_minimal provable
  primordial_mem := rfl
  counter_mem := rfl
  primordial_nonbot := by decide
  counter_nonbot := by decide
  orthogonal := rfl
  primordial_in_support := le_refl _
  map_bot := rfl
  primordial_minimal := by
    -- Only x = left satisfies: nucleus x = x, ⊥ < x, x ≤ left
    intro x _ hne hsup
    cases x with
    | bot => exact absurd rfl (ne_of_gt hne)
    | left => exact le_refl _
    | right => exact absurd hsup (by decide)  -- right ≤ left is false
    | top => exact absurd hsup (by decide)    -- top ≤ left is false

end Diamond

/-! ## Verification -/

section Verification

def verifyAllDiamondRoundTrips : Bool :=
  Diamond.idClose .bot == .bot &&
  Diamond.idClose .left == .left &&
  Diamond.idClose .right == .right &&
  Diamond.idClose .top == .top

#eval verifyAllDiamondRoundTrips

def verifyDiamondOrthogonal : Bool :=
  (Diamond.left ⊓ Diamond.right) == Diamond.bot

#eval verifyDiamondOrthogonal

def verifyDiamondClosure : Bool :=
  (Diamond.idClose (Diamond.idClose .left) == Diamond.idClose .left) &&
  (Diamond.idClose (Diamond.idClose .right) == Diamond.idClose .right) &&
  decide (Diamond.left ≤ Diamond.idClose .left) &&
  decide (Diamond.right ≤ Diamond.idClose .right)

#eval verifyDiamondClosure

def verifyDiamondHimp : Bool :=
  (Diamond.bot ⇨ Diamond.left) == Diamond.top &&
  (Diamond.bot ⇨ Diamond.right) == Diamond.top &&
  (Diamond.left ⇨ Diamond.left) == Diamond.top &&
  (Diamond.right ⇨ Diamond.right) == Diamond.top &&
  (Diamond.left ⇨ Diamond.bot) == Diamond.right &&
  (Diamond.right ⇨ Diamond.bot) == Diamond.left

#eval verifyDiamondHimp

def verifyDistributive : Bool :=
  let test (x y z : Diamond) := (x ⊓ (y ⊔ z)) == ((x ⊓ y) ⊔ (x ⊓ z))
  test .left .right .bot &&
  test .top .left .right &&
  test .left .top .bot

#eval verifyDistributive

end Verification

end ComputableTestKit
end Bridges
end Tests
end HeytingLean
