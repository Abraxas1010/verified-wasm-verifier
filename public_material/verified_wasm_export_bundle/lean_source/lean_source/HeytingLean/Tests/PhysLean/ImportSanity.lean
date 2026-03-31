/-
Copyright (c) 2026 HeytingLean contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import PhysLean.Relativity.Tensors.RealTensor.Vector.Basic
import PhysLean.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct
import PhysLean.Relativity.Tensors.RealTensor.Vector.Causality.Basic
import PhysLean.Relativity.LorentzGroup.Boosts.Generalized

/-!
# PhysLean Import Sanity Check

This file verifies that PhysLean modules can be imported into HeytingLean.
The PhysLean library has been backported from Mathlib v4.26 to v4.24.0.

## Available Modules

The following PhysLean modules are available (among others):
- Lorentz vectors and Minkowski product
- Causal structure (timelike, lightlike, spacelike)
- Lorentz group and generalized boosts
- SpaceTime basics

## Known Limitations

12 PhysLean modules have known issues with the v4.24 backport.
See BACKPORT_STATUS.md in the PhysLean repository for details.
-/

namespace HeytingLean.Tests.PhysLean

open Lorentz

-- Basic vector type is available
#check Vector

-- Minkowski product
#check Vector.minkowskiProduct

-- Generalized boosts
#check LorentzGroup.generalizedBoost

-- Causal character (from Causality module)
#check Vector.causalCharacter

end HeytingLean.Tests.PhysLean
