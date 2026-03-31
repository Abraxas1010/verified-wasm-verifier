namespace HeytingLean.LeanCP

/-- Memory permissions ordered by strength. -/
inductive Perm where
  | Freeable
  | Writable
  | Readable
  | Nonempty
  deriving DecidableEq, Repr, Inhabited

namespace Perm

/-- Boolean ordering used by the memory model. -/
def le : Perm → Perm → Bool
  | .Nonempty, _ => true
  | .Readable, .Readable => true
  | .Readable, .Writable => true
  | .Readable, .Freeable => true
  | .Writable, .Writable => true
  | .Writable, .Freeable => true
  | .Freeable, .Freeable => true
  | _, _ => false

/-- Read permission predicate. -/
def allowsRead : Perm → Prop
  | .Freeable | .Writable | .Readable => True
  | .Nonempty => False

/-- Write permission predicate. -/
def allowsWrite : Perm → Prop
  | .Freeable | .Writable => True
  | .Readable | .Nonempty => False

/-- Free permission predicate. -/
def allowsFree : Perm → Prop
  | .Freeable => True
  | .Writable | .Readable | .Nonempty => False

instance instDecidableAllowsRead (p : Perm) : Decidable (allowsRead p) := by
  cases p with
  | Freeable => exact isTrue trivial
  | Writable => exact isTrue trivial
  | Readable => exact isTrue trivial
  | Nonempty => exact isFalse (by intro h; cases h)

instance instDecidableAllowsWrite (p : Perm) : Decidable (allowsWrite p) := by
  cases p with
  | Freeable => exact isTrue trivial
  | Writable => exact isTrue trivial
  | Readable => exact isFalse (by intro h; cases h)
  | Nonempty => exact isFalse (by intro h; cases h)

instance instDecidableAllowsFree (p : Perm) : Decidable (allowsFree p) := by
  cases p with
  | Freeable => exact isTrue trivial
  | Writable => exact isFalse (by intro h; cases h)
  | Readable => exact isFalse (by intro h; cases h)
  | Nonempty => exact isFalse (by intro h; cases h)

theorem allowsRead_of_allowsWrite {p : Perm} (h : allowsWrite p) : allowsRead p := by
  cases p <;> simp [allowsWrite, allowsRead] at h ⊢

theorem allowsWrite_of_allowsFree {p : Perm} (h : allowsFree p) : allowsWrite p := by
  cases p <;> simp [allowsFree, allowsWrite] at h ⊢

theorem allowsRead_of_allowsFree {p : Perm} (h : allowsFree p) : allowsRead p := by
  exact allowsRead_of_allowsWrite (allowsWrite_of_allowsFree h)

theorem le_refl (p : Perm) : le p p = true := by
  cases p <;> rfl

theorem le_trans {p q r : Perm} (hpq : le p q = true) (hqr : le q r = true) :
    le p r = true := by
  cases p <;> cases q <;> cases r <;> simp [le] at hpq hqr ⊢

end Perm
end HeytingLean.LeanCP
