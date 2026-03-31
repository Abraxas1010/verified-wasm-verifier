import Mathlib.Algebra.Order.Quantale
import Mathlib.Data.Set.Image
import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Frame → (commutative, unital) quantale via meet

Mathlib models quantales via the mixin `IsQuantale` on top of `Semigroup` and `CompleteLattice`
(`Mathlib/Algebra/Order/Quantale`). This file provides a lightweight “logic-channel” wrapper:

* start with a frame `α` (i.e. complete Heyting algebra / locale),
* view it as a quantale by taking `(*) := (⊓)` and (optionally) `1 := ⊤`.

We deliberately place the `Mul`/`One` instances on a dedicated type wrapper to avoid interfering with
any pre-existing multiplication on `α`.
-/

namespace HeytingLean
namespace CPP

universe u

/-- Type wrapper for equipping a frame with `(*) := (⊓)` (“logic-channel” tensor). -/
structure MeetQuantale (α : Type u) : Type u where
  /-- Underlying element. -/
  val : α

namespace MeetQuantale

variable {α : Type u}

instance : Coe (MeetQuantale α) α :=
  ⟨MeetQuantale.val⟩

instance : CoeTC α (MeetQuantale α) :=
  ⟨fun a => ⟨a⟩⟩

@[simp] lemma coe_mk (a : α) : ((⟨a⟩ : MeetQuantale α) : α) = a := rfl

@[simp] lemma mk_coe (a : MeetQuantale α) : ((a : α) : MeetQuantale α) = a := by
  cases a
  rfl

@[ext] lemma ext {a b : MeetQuantale α} (h : (a : α) = (b : α)) : a = b := by
  cases a
  cases b
  cases h
  rfl

instance instCompleteLattice [CompleteLattice α] : CompleteLattice (MeetQuantale α) where
  le a b := (a : α) ≤ (b : α)
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans
  le_antisymm a b hab hba := by
    ext
    exact le_antisymm hab hba
  sup a b := ⟨(a : α) ⊔ (b : α)⟩
  le_sup_left _ _ := le_sup_left
  le_sup_right _ _ := le_sup_right
  sup_le _ _ _ hac hbc := sup_le hac hbc
  inf a b := ⟨(a : α) ⊓ (b : α)⟩
  inf_le_left _ _ := inf_le_left
  inf_le_right _ _ := inf_le_right
  le_inf _ _ _ hac hbc := le_inf hac hbc
  top := ⟨(⊤ : α)⟩
  le_top _ := le_top
  bot := ⟨(⊥ : α)⟩
  bot_le _ := bot_le
  sSup s := ⟨sSup ((fun x : MeetQuantale α => (x : α)) '' s)⟩
  le_sSup s a ha :=
    _root_.le_sSup (s := (fun x : MeetQuantale α => (x : α)) '' s) (a := (a : α)) ⟨a, ha, rfl⟩
  sSup_le s a ha := by
    refine _root_.sSup_le ?_
    intro b hb
    rcases hb with ⟨b', hb', rfl⟩
    exact ha b' hb'
  sInf s := ⟨sInf ((fun x : MeetQuantale α => (x : α)) '' s)⟩
  sInf_le s a ha :=
    _root_.sInf_le (s := (fun x : MeetQuantale α => (x : α)) '' s) (a := (a : α)) ⟨a, ha, rfl⟩
  le_sInf s a ha := by
    refine _root_.le_sInf ?_
    intro b hb
    rcases hb with ⟨b', hb', rfl⟩
    exact ha b' hb'

@[simp] lemma coe_sSup [CompleteLattice α] (s : Set (MeetQuantale α)) :
    ((sSup s : MeetQuantale α) : α) = sSup ((fun x : MeetQuantale α => (x : α)) '' s) :=
  rfl

@[simp] lemma coe_sInf [CompleteLattice α] (s : Set (MeetQuantale α)) :
    ((sInf s : MeetQuantale α) : α) = sInf ((fun x : MeetQuantale α => (x : α)) '' s) :=
  rfl

instance instMul [SemilatticeInf α] : Mul (MeetQuantale α) :=
  ⟨fun a b => ⟨(a : α) ⊓ (b : α)⟩⟩

instance instOne [Top α] : One (MeetQuantale α) :=
  ⟨⟨(⊤ : α)⟩⟩

@[simp] lemma mul_def [SemilatticeInf α] (a b : MeetQuantale α) :
    ((a * b : MeetQuantale α) : α) = (a : α) ⊓ (b : α) := rfl

@[simp] lemma one_def [Top α] : ((1 : MeetQuantale α) : α) = (⊤ : α) := rfl

instance instSemigroup [SemilatticeInf α] : Semigroup (MeetQuantale α) where
  mul_assoc a b c := by
    ext
    simp [mul_def, inf_assoc]

instance instCommSemigroup [SemilatticeInf α] : CommSemigroup (MeetQuantale α) where
  mul_comm a b := by
    ext
    simp [mul_def, inf_comm]
  mul_assoc a b c := by
    ext
    simp [mul_def, inf_assoc]

instance instMonoid [SemilatticeInf α] [OrderTop α] : Monoid (MeetQuantale α) where
  mul_assoc a b c := by
    ext
    simp [mul_def, inf_assoc]
  one_mul a := by
    ext
    simp
  mul_one a := by
    ext
    simp

instance instCommMonoid [SemilatticeInf α] [OrderTop α] : CommMonoid (MeetQuantale α) where
  mul_assoc a b c := by
    ext
    simp [mul_def, inf_assoc]
  one_mul a := by
    ext
    simp
  mul_one a := by
    ext
    simp
  mul_comm a b := by
    ext
    simp [mul_def, inf_comm]

instance instIsQuantale [Order.Frame α] : IsQuantale (MeetQuantale α) where
  mul_sSup_distrib x s := by
    -- Rewrite the `⨆` into an `sSup` over an image, then apply the frame distributivity lemma in `α`.
    rw [← (_root_.sSup_image (s := s) (f := fun y : MeetQuantale α => x * y))]
    ext
    simp [mul_def, Set.image_image]
    calc
      (x : α) ⊓ sSup ((fun y : MeetQuantale α => (y : α)) '' s)
          = ⨆ b ∈ ((fun y : MeetQuantale α => (y : α)) '' s), (x : α) ⊓ b := by
              simpa using (_root_.inf_sSup_eq (a := (x : α)) (s := (fun y : MeetQuantale α => (y : α)) '' s))
      _ = sSup ((fun b : α => (x : α) ⊓ b) '' ((fun y : MeetQuantale α => (y : α)) '' s)) := by
              symm
              simpa using (_root_.sSup_image (s := (fun y : MeetQuantale α => (y : α)) '' s) (f := fun b : α => (x : α) ⊓ b))
      _ = sSup ((fun a : MeetQuantale α => (x : α) ⊓ (a : α)) '' s) := by
              simp [Set.image_image]
  sSup_mul_distrib s x := by
    rw [← (_root_.sSup_image (s := s) (f := fun y : MeetQuantale α => y * x))]
    ext
    simp [mul_def, Set.image_image]
    calc
      sSup ((fun y : MeetQuantale α => (y : α)) '' s) ⊓ (x : α)
          = ⨆ b ∈ ((fun y : MeetQuantale α => (y : α)) '' s), b ⊓ (x : α) := by
              simpa using
                (_root_.sSup_inf_eq (s := (fun y : MeetQuantale α => (y : α)) '' s) (b := (x : α)))
      _ = sSup ((fun b : α => b ⊓ (x : α)) '' ((fun y : MeetQuantale α => (y : α)) '' s)) := by
              symm
              simpa using (_root_.sSup_image (s := (fun y : MeetQuantale α => (y : α)) '' s) (f := fun b : α => b ⊓ (x : α)))
      _ = sSup ((fun a : MeetQuantale α => (a : α) ⊓ (x : α)) '' s) := by
              simp [Set.image_image]

end MeetQuantale

end CPP
end HeytingLean
