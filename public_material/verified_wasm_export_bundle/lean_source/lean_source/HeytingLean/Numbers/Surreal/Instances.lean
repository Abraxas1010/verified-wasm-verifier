import HeytingLean.Numbers.Surreal.QuotOps
import HeytingLean.Numbers.Surreal.Embeddings

namespace HeytingLean
namespace Numbers
namespace Surreal

/-!
Typeclass instances and convenient numerals for `SurrealQ`.
-/

noncomputable instance : Zero SurrealQ where
  zero := zeroQ

noncomputable instance : Add SurrealQ where
  add := addQ

noncomputable instance : Neg SurrealQ where
  neg := negQ

noncomputable instance : Mul SurrealQ where
  mul := mulQ

/-- `1` as a quotient surreal (dyadic 1). -/
noncomputable def oneQ : SurrealQ := ofDyadic { num := Int.ofNat 1, pow := 0 }

noncomputable instance : One SurrealQ where
  one := oneQ

/-- Embed a natural number as a quotient surreal. -/
noncomputable def ofNatQ (n : Nat) : SurrealQ :=
  ofDyadic { num := Int.ofNat n, pow := 0 }

/-- Embed an integer as a quotient surreal. -/
noncomputable def ofIntQ (z : Int) : SurrealQ :=
  ofDyadic { num := z, pow := 0 }

noncomputable instance (n : Nat) : OfNat SurrealQ n where
  ofNat := ofNatQ n

end Surreal
end Numbers
end HeytingLean

