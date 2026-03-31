/-
Copyright (c) 2026 HeytingLean Authors. All rights reserved.
Released under Apache 2.0 license.
-/

import Mathlib.CategoryTheory.Triangulated.Basic
import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Derived Categories Bridge

This module provides a bridge between Mathlib's derived category formalization
and HeytingLean's computational homology infrastructure.

## Main References

- Joël Riou, "Formalization of derived categories in Lean/Mathlib" (2024)
  https://afm.episciences.org/15978

## What's Available from Mathlib

The following are now formalized in Mathlib (since May 2024):

1. **Derived Category Construction**
   - `DerivedCategory C` : The derived category D(C) of an abelian category C
   - Constructed as localization of unbounded cochain complexes
   - Localized with respect to quasi-isomorphisms

2. **Triangulated Structure**
   - `HomotopyCategory.triangulated` : Triangulated structure on homotopy categories
   - Localization theorem: triangulated structure descends through localization

3. **Key Definitions**
   - `QuasiIso` : The class of quasi-isomorphisms
   - `HomotopyCategory` : Category of cochain complexes up to homotopy
   - `DerivedCategory.Q` : The localization functor K(C) → D(C)

## HeytingLean Integration Points

- `HeytingLean.Computational.Homology` : Computational homology over F₂
- `HeytingLean.Topos.LocSys.ChainComplexes` : Chain complexes on local systems

-/

namespace HeytingLean.CategoryTheory

open CategoryTheory

/-! ## Re-exports for convenience -/

-- The derived category of an abelian category
#check @DerivedCategory

-- Homotopy category with triangulated structure
#check @HomotopyCategory

-- Quasi-isomorphisms (the morphisms we localize at)
#check @CategoryTheory.MorphismProperty

/-! ## Bridge Structures

These structures connect Mathlib's abstract derived categories
to HeytingLean's computational homology.
-/

/-- Configuration for derived category computations in HeytingLean -/
structure DerivedConfig where
  /-- Whether to use computational (F₂) or abstract coefficients -/
  computational : Bool := true
  /-- Maximum chain complex length for computations -/
  maxLength : Nat := 100

/-! ## Future Work

1. Connect to `HeytingLean.Computational.Homology.ChainComplex` for F₂ computations
2. Implement spectral sequence computations using derived functors
3. Bridge to `HeytingLean.Topos.LocSys` for sheaf cohomology
4. Add computational tools for Ext and Tor functors
-/

end HeytingLean.CategoryTheory
