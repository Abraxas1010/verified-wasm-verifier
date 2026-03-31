import HeytingLean.Chem.Materials.Symmetry.AffineGroup
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Seed space-group definitions (generator-based)

This module defines a "space group" as a subgroup of affine operations on fractional coordinates.
To avoid shipping large enumerations of operations initially, we build groups from small lists of
generators (via `Subgroup.closure`).

The seed catalog here is intentionally small; it exists to make materials benchmarks executable
and to give future work a place to land larger, provenance-backed space-group datasets.
-/

namespace HeytingLean.Chem.Materials.Symmetry

open HeytingLean.Chem.Materials

abbrev SpaceGroup (d : Nat) : Type := Subgroup (AffineOpG d)

def SpaceGroup.ofGenerators {d : Nat} (gens : List (AffineOpG d)) : SpaceGroup d :=
  Subgroup.closure (fun g => g ∈ gens)

def P1 (d : Nat) : SpaceGroup d :=
  ⊥

namespace Seed

def vec3 (a b c : ℚ) : FracCoord 3
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

def translation3 (b : FracCoord 3) : AffineOpG 3 :=
  { A := 1
    b := b }

-- A small "F-centering translation" seed (used by FCC-based materials).
def fccCenterTranslations : SpaceGroup 3 :=
  SpaceGroup.ofGenerators
    [ translation3 (vec3 0 (1/2) (1/2))
    , translation3 (vec3 (1/2) 0 (1/2))
    , translation3 (vec3 (1/2) (1/2) 0)
    ]

-- A minimal nontrivial point-symmetry seed: sign flips about coordinate axes.
def diag3 (a b c : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  Matrix.diagonal (fun i : Fin 3 =>
    match i.1 with
    | 0 => a
    | 1 => b
    | _ => c)

def diagGL3 (a b c : ℚ) (h : Matrix.det (diag3 a b c) ≠ 0) : Matrix.GeneralLinearGroup (Fin 3) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (diag3 a b c) h

def flipX : AffineOpG 3 :=
  { A := diagGL3 (-1) 1 1 (by
      -- det = -1
      simp [diag3, Matrix.det_diagonal]
      native_decide)
    b := vec3 0 0 0 }

def flipY : AffineOpG 3 :=
  { A := diagGL3 1 (-1) 1 (by
      simp [diag3, Matrix.det_diagonal]
      native_decide)
    b := vec3 0 0 0 }

def flipZ : AffineOpG 3 :=
  { A := diagGL3 1 1 (-1) (by
      simp [diag3, Matrix.det_diagonal]
      native_decide)
    b := vec3 0 0 0 }

def cubicSignFlips : SpaceGroup 3 :=
  SpaceGroup.ofGenerators [flipX, flipY, flipZ]

-- A benchmark-oriented seed for FCC materials: combine FCC translations with a small point-group seed.
def fccSeed : SpaceGroup 3 :=
  SpaceGroup.ofGenerators
    [ translation3 (vec3 0 (1/2) (1/2))
    , translation3 (vec3 (1/2) 0 (1/2))
    , translation3 (vec3 (1/2) (1/2) 0)
    , flipX, flipY, flipZ
    ]

end Seed

end HeytingLean.Chem.Materials.Symmetry
