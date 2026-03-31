import HeytingLean.Chem.Materials.Symmetry.Affine
import Mathlib.Tactic

/-!
# Symmetry affine-op smoke test
-/

namespace HeytingLean
namespace Chem
namespace Tests

open HeytingLean.Chem.Materials
open HeytingLean.Chem.Materials.Symmetry

def vec2 (a b : ℚ) : FracCoord 2
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b

def idMat2 : IntMat 2 :=
  fun i j => if i = j then 1 else 0

def idOp2 : AffineOp 2 :=
  { A := idMat2
    b := vec2 0 0 }

example : idOp2.apply (vec2 (1/3) (2/3)) = vec2 (1/3) (2/3) := by
  funext i
  fin_cases i <;> simp [AffineOp.apply, idOp2, idMat2, vec2]

end Tests
end Chem
end HeytingLean

