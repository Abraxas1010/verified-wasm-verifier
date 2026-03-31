import HeytingLean.Bridges.Geo

/-!
# Lenses.Geometric

Compatibility re-export for legacy `HeytingLean/Lenses/Geometric` imports.
-/

namespace HeytingLean.Lenses.Geometric

abbrev Model (α : Type _) [HeytingLean.LoF.PrimaryAlgebra α] :=
  HeytingLean.Bridges.Geo.Model (α := α)

section
variable {α : Type _} [HeytingLean.LoF.PrimaryAlgebra α]

/-- Legacy round-trip theorem name (decode after encode). -/
@[simp] theorem decode_encode (M : Model α) (a : M.R.Omega) :
    M.decode (M.contract.encode a) = a :=
  M.contract.round a

/-- Legacy dual round-trip direction (encode after decode on carrier). -/
@[simp] theorem encode_decode (M : Model α) (c : M.Carrier) :
    M.encode (M.decode c) = c :=
  HeytingLean.Bridges.Geo.Model.encode_decode (M := M) c

end

end HeytingLean.Lenses.Geometric
