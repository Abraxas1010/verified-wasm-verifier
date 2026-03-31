/-
Lightweight tensor core primitives (compile-friendly).
We avoid heavy numeric dependencies; vectors are Arrays of Float with
recorded dimension.
-/

namespace HeytingLean
namespace Computational
namespace Tensor

structure EmbVec where
  dim : Nat
  data : Array Float

namespace EmbVec

@[simp] def zeros (n : Nat) : EmbVec :=
  { dim := n, data := Array.replicate n 0.0 }

@[simp] def ofList (xs : List Float) : EmbVec :=
  { dim := xs.length, data := Array.mk xs }

@[simp] def length (v : EmbVec) : Nat := v.dim

end EmbVec

/-- A core transform stands in for a tensor operator in embedding space. -/
abbrev CoreTransform := EmbVec → EmbVec

end Tensor
end Computational
end HeytingLean
