/-
  Integration with Lean's built-in `Subtype`.
  Provides bidirectional conversions and an equivalence.
-/

import HeytingLean.Certified.Basic
import Mathlib.Logic.Equiv.Defs

namespace HeytingLean
namespace Certified

universe u

/-- Convert `Subtype` to `Certified`. -/
def fromSubtype {α : Type u} {P : α → Prop} (s : Subtype P) : Certified α P :=
  ⟨s.val, s.property⟩

/-- Convert `Certified` to `Subtype`. -/
def toSubtype {α : Type u} {P : α → Prop} (c : Certified α P) : Subtype P :=
  ⟨c.val, c.ok⟩

/-- Equivalence between `Certified` and `Subtype`. -/
def certifiedSubtypeEquiv {α : Type u} {P : α → Prop} : Equiv (Certified α P) (Subtype P) where
  toFun := toSubtype
  invFun := fromSubtype
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Certified naturals bounded above. -/
abbrev CertifiedNat (n : Nat) : Type := Certified Nat (fun m => m < n)

/-- Certified non-empty list. -/
abbrev CertifiedNonEmpty (α : Type u) : Type u := Certified (List α) (fun xs => xs.length > 0)

/-- Certified positive natural. -/
abbrev CertifiedPos : Type := Certified Nat (fun n => n > 0)

end Certified
end HeytingLean
