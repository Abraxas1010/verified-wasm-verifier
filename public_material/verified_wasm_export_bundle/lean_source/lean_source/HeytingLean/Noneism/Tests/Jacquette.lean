import HeytingLean.Noneism.Semantics.Jacquette
import HeytingLean.Noneism.Semantics.LP

namespace HeytingLean
namespace Noneism
namespace Tests

open Jacquette

namespace Demo
def D := Unit
def both : Jacquette.Property D := { eval := fun _ => ⟨true, true⟩ }
def falseOnly : Jacquette.Property D := { eval := fun _ => ⟨false, true⟩ }
end Demo

theorem jacquette_smoke :
    Jacquette.ident (a := ()) (b := ()) ∧
    Jacquette.designated Demo.both () ∧
    ¬ Jacquette.designated Demo.falseOnly () := by
  refine And.intro ?h1 (And.intro ?h2 ?h3)
  · simpa using Jacquette.ident_refl ()
  · simp [Jacquette.designated, Demo.both, LP.TV.designated]
  · simp [Jacquette.designated, Demo.falseOnly, LP.TV.designated]

/-- Symmetry of intensional identity (unit witness). -/
theorem jacquette_symm :
    Jacquette.ident (a := ()) (b := ()) → Jacquette.ident (a := ()) (b := ()) := by
  intro h; simpa using (Jacquette.ident_symm (a := ()) (b := ()) h)

/-- Transitivity of intensional identity (unit witness). -/
theorem jacquette_trans :
    Jacquette.ident (a := ()) (b := ()) →
    Jacquette.ident (a := ()) (b := ()) →
    Jacquette.ident (a := ()) (b := ()) := by
  intro h1 h2; simpa using (Jacquette.ident_trans (a := ()) (b := ()) (c := ()) h1 h2)

end Tests
end Noneism
end HeytingLean
