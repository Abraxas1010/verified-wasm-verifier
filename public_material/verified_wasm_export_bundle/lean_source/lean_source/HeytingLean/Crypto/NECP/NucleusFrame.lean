import Mathlib.Order.Nucleus

namespace HeytingLean
namespace Crypto
namespace NECP

universe u

/-- Local NECP-facing alias for the Mathlib nucleus frame carrier. -/
abbrev NuclearFrame (F : Type u) [Order.Frame F] := Nucleus F

section

variable {F : Type u} [Order.Frame F]

instance : Order.Frame (NuclearFrame F) := inferInstance
instance : CompleteLattice (NuclearFrame F) := inferInstance

/-- Fixed points of a nucleus, exposed as a set for protocol-facing bookkeeping. -/
def fixedPoints (n : NuclearFrame F) : Set F := {x | n x = x}

@[simp] theorem mem_fixedPoints {n : NuclearFrame F} {x : F} :
    x ∈ fixedPoints n ↔ n x = x :=
  Iff.rfl

@[simp] theorem top_mem_fixedPoints (n : NuclearFrame F) :
    (⊤ : F) ∈ fixedPoints n := by
  simp [fixedPoints]

@[simp] theorem apply_inf (n : NuclearFrame F) (x y : F) :
    n (x ⊓ y) = n x ⊓ n y :=
  Nucleus.map_inf (n := n) (x := x) (y := y)

@[simp] theorem apply_himp_fixed_right (n : NuclearFrame F) (x y : F)
    (hy : n y = y) : n (x ⇨ y) = x ⇨ y := by
  simpa [hy] using n.map_himp_apply x y

end

end NECP
end Crypto
end HeytingLean
