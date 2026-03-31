import Mathlib.Data.Bool.Basic

set_option autoImplicit false

namespace HeytingLean.Physics.FreeWill

/-- Exactly one value is `false` in the triple `(a,b,c)`. -/
def ExactlyOneFalse (a b c : Bool) : Prop :=
  (a = false ∧ b = true ∧ c = true) ∨
  (a = true ∧ b = false ∧ c = true) ∨
  (a = true ∧ b = true ∧ c = false)

@[simp] theorem exactlyOneFalse_ff_tt_tt : ExactlyOneFalse false true true := by
  left
  exact ⟨rfl, rfl, rfl⟩

@[simp] theorem exactlyOneFalse_tt_ff_tt : ExactlyOneFalse true false true := by
  right
  left
  exact ⟨rfl, rfl, rfl⟩

@[simp] theorem exactlyOneFalse_tt_tt_ff : ExactlyOneFalse true true false := by
  right
  right
  exact ⟨rfl, rfl, rfl⟩

/-- A frame is an orthogonal triple of directions. -/
structure Frame (Dir : Type*) (Orth : Dir → Dir → Prop) where
  x : Dir
  y : Dir
  z : Dir
  orth_xy : Orth x y
  orth_xz : Orth x z
  orth_yz : Orth y z

/-- A `101` valuation has exactly one `false` in every orthogonal frame. -/
def Is101 {Dir : Type*} (Orth : Dir → Dir → Prop) (θ : Dir → Bool) : Prop :=
  ∀ f : Frame Dir Orth, ExactlyOneFalse (θ f.x) (θ f.y) (θ f.z)

end HeytingLean.Physics.FreeWill
