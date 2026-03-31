import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types.Basic
import HeytingLean.Physics.String.ModularQ
import HeytingLean.Physics.String.WorldsheetCobordism

/-!
# SegalFunctor (Track A)

Minimal “CFT as functor” scaffold.

We do not claim to encode full Segal axioms or analytic CFT. Instead:
- `Boundary` (from `WorldsheetCobordism`) forms a category, with worldsheets as morphisms.
- Given finite modular matrices `S,T`, a worldsheet’s generator list is interpreted as a
  compositional operator on truncated `QSeries`.

This creates a concrete, executable target for later refinement:
we can test coherence (functor laws) and run demos without extra axioms.
-/

namespace HeytingLean
namespace Physics
namespace String

open CategoryTheory

namespace Worldsheet

/-- Interpret one generator as a `QSeries → QSeries` update. -/
def applyGen (M : ModMatrices) (g : Generator) (q : QSeries) : QSeries :=
  match g with
  | .S => { coeffs := applyMat M.S q.coeffs }
  | .T => { coeffs := applyMat M.T q.coeffs }

/-- Interpret a generator chain as sequential application on `QSeries`. -/
def applyGens (M : ModMatrices) (gs : List Generator) (q : QSeries) : QSeries :=
  gs.foldl (fun q' g => applyGen M g q') q

theorem applyGens_nil (M : ModMatrices) (q : QSeries) : applyGens M [] q = q := by
  simp [applyGens]

theorem applyGens_append (M : ModMatrices) (xs ys : List Generator) (q : QSeries) :
    applyGens M (xs ++ ys) q = applyGens M ys (applyGens M xs q) := by
  -- `foldl` over append is sequential composition.
  simp [applyGens, List.foldl_append]

end Worldsheet

/-- A concrete functor from `Boundary` to `Type`, interpreting worldsheets as operators on `QSeries`. -/
def qSeriesFunctor (M : ModMatrices) : Boundary ⥤ Type where
  obj _ := QSeries
  map {A B} (W : A ⟶ B) := fun q => Worldsheet.applyGens M W.gens q
  map_id := by
    intro A
    funext q
    -- `𝟙 A` is the empty generator chain.
    change Worldsheet.applyGens M (Worldsheet.id A).gens q = q
    simp [Worldsheet.id, Worldsheet.applyGens]
  map_comp := by
    intro A B C W₁ W₂
    funext q
    -- `comp` is `sew`, which appends generator chains.
    simpa [Worldsheet.sew] using
      (Worldsheet.applyGens_append (M := M) (xs := W₁.gens) (ys := W₂.gens) (q := q))

end String
end Physics
end HeytingLean
