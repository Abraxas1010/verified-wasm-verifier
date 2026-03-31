/-
  Erasure markers for controlling what gets compiled vs erased.

  Key principle:
  - Types in `Type` compile to runtime code
  - Types in `Prop` are erased (proof-irrelevant)
-/

namespace HeytingLean
namespace Erasure

universe u v

/-- Marker for runtime-relevant computations. -/
class Runtime (α : Type u) where
  /-- Hint that this type should compile. -/
  compileHint : Unit := ()

/-- Marker for proof-only content (will be erased). -/
class ProofOnly (α : Prop) where
  /-- Hint that this is erased. -/
  eraseHint : Unit := ()

/-- Computational content: explicitly mark as runtime-relevant. -/
structure Comp (α : Type u) where
  val : α
deriving Repr

/-- Ghost content: carried for specification; erased when `α` is a `Prop`. -/
structure Ghost (α : Sort u) where
  val : α

/-- Extract computational content. -/
@[inline] def Comp.run {α : Type u} (c : Comp α) : α := c.val

/-- Ghosts over `Prop` are proof-irrelevant. -/
theorem Ghost.irrelevant {α : Prop} (g₁ g₂ : Ghost α) : g₁ = g₂ := by
  cases g₁ with
  | mk h₁ =>
    cases g₂ with
    | mk h₂ =>
      have : h₁ = h₂ := Subsingleton.elim _ _
      cases this
      rfl

/-- Separation: pair computational and ghost content. -/
structure Separated (α : Type u) (β : Sort v) where
  comp : Comp α
  ghost : Ghost β

namespace Separated

/-- Extract only the computational part from `Separated`. -/
@[inline] def extract {α : Type u} {β : Sort v} (s : Separated α β) : α :=
  s.comp.val

end Separated

end Erasure
end HeytingLean

