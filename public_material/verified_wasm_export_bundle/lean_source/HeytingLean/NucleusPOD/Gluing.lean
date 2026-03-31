import HeytingLean.NucleusPOD.Foundation

namespace HeytingLean
namespace NucleusPOD

/-!
Layer 3: Sheaf Gluing and Transport
Generated from `NucleusPOD_Lean_Proof_Catalog.docx`.
-/

def glueSections (g : GluingData) : Nat :=
  closure (Nat.max g.leftSection g.rightSection)

theorem gluing_unique (g : GluingData) :
    glueSections g = closure (Nat.max g.rightSection g.leftSection) := by
  simp [glueSections, Nat.max_comm]

theorem gluing_R_closed (g : GluingData) : closure (glueSections g) = glueSections g := by
  unfold glueSections
  exact closure_idempotent (Nat.max g.leftSection g.rightSection)

end NucleusPOD
end HeytingLean
