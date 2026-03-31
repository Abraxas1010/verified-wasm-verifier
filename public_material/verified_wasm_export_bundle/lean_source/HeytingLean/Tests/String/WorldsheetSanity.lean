import HeytingLean.Physics.String.SegalFunctor
import HeytingLean.Physics.String.ModularNucleusLaws

/-!
# String.WorldsheetSanity

Smoke-level but nontrivial checks for the Track-A worldsheet/cobordism + functor layer:
- `Boundary` forms a category with `Worldsheet` morphisms and `sew` as composition.
- The `qSeriesFunctor` respects composition by construction.
- The predicate-level modular nucleus is provably idempotent.
-/

namespace HeytingLean
namespace Tests
namespace String

open HeytingLean.Physics.String
open CategoryTheory

def brA : Brane := { label := "A" }
def brB : Brane := { label := "B" }

def bClosed : Boundary := .closed
def bOpenAB : Boundary := .open brA brB

def Wst (A B : Boundary) (gs : List Generator) : Worldsheet A B :=
  { surface := { genus := 0, punctures := 2 }, gens := gs }

def W1 : bClosed ⟶ bClosed := Wst bClosed bClosed [.S, .T]
def W2 : bClosed ⟶ bClosed := Wst bClosed bClosed [.T]

theorem comp_gens :
    (W1 ≫ W2).gens = W1.gens ++ W2.gens := by
  rfl

def mats2 : ModMatrices :=
  { S := #[#[1.0, 0.0], #[0.0, 1.0]]
    T := #[#[0.0, 1.0], #[1.0, 0.0]]
  }

def q0 : QSeries := { coeffs := #[10.0, 20.0] }

theorem functor_comp :
    (qSeriesFunctor mats2).map (W1 ≫ W2) q0
      = (qSeriesFunctor mats2).map W2 ((qSeriesFunctor mats2).map W1 q0) := by
  -- This is exactly the functor law; `simp` should reduce it.
  simp [qSeriesFunctor]

theorem modular_close_idem (P : Partition → Prop) :
    ModularNucleus.close (ModularNucleus.close P) = ModularNucleus.close P := by
  simpa using (ModularNucleus.close_close (P := P))

end String
end Tests
end HeytingLean

