import HeytingLean.Bridges.Clifford

/-!
# Lenses.Clifford

Compatibility re-export for legacy `HeytingLean/Lenses/Clifford` imports.
-/

namespace HeytingLean.Lenses.Clifford

abbrev Model := HeytingLean.Bridges.Clifford.Model

section
variable {α : Type _} [HeytingLean.LoF.PrimaryAlgebra α]

/-- Legacy round-trip theorem name (decode after encode). -/
@[simp] theorem decode_encode (M : Model α) (a : M.R.Omega) :
    M.decode (M.contract.encode a) = a :=
  HeytingLean.Bridges.Clifford.Model.decode_encode M a

/-- Carrier-side round-trip lands in the projector-fixed shadow. -/
@[simp] theorem encode_decode_project (M : Model α) (c : M.Carrier) :
    M.encode (M.decode c) = M.project c := by
  cases c
  simp [HeytingLean.Bridges.Clifford.Model.encode,
    HeytingLean.Bridges.Clifford.Model.decode,
    HeytingLean.Bridges.Clifford.Model.project]

end

end HeytingLean.Lenses.Clifford
