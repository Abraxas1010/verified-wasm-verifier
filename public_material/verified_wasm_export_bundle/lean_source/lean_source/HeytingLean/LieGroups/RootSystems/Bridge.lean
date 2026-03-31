/-
Copyright (c) 2026 Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/
import Mathlib.Algebra.Lie.Weights.RootSystem

/-!
# Root Systems Bridge

This module is an optional bridge into Mathlib's root system / Weyl group
infrastructure for semisimple Lie algebras.

The intent is to provide a stable import and a minimal re-export surface so
downstream code can rely on these objects without repeating heavy imports.
-/

set_option autoImplicit false

namespace HeytingLean.LieGroups.RootSystems

-- This file intentionally stays thin. Downstream projects can add more wrappers
-- once a concrete semisimple Lie algebra workflow is selected.

end HeytingLean.LieGroups.RootSystems

