/-
Copyright (c) 2026 Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.LieGroups.Basic
import HeytingLean.LieGroups.Actions.SmoothAction
import HeytingLean.LieGroups.Actions.Infinitesimal
import HeytingLean.LieGroups.Matrix.GLExp
import HeytingLean.LieGroups.Matrix.Adjoint
import HeytingLean.LieGroups.Measure.HaarAveraging
import HeytingLean.LieGroups.Rep.Basic
import HeytingLean.LieGroups.RootSystems.Bridge
import HeytingLean.LieGroups.SmokeTest

/-!
# Lie Groups Utility Stack

This module re-exports the complete Lie Groups utility stack for HeytingLean.

## Contents

* `LieGroups.Basic` — Lie algebra definition, smoothness lemmas
* `LieGroups.Actions.SmoothAction` — `ContMDiffMulAction` class
* `LieGroups.Actions.Infinitesimal` — infinitesimal action, fundamental vector fields
* `LieGroups.Matrix.GLExp` — matrix exponential into GL, one-parameter subgroups
* `LieGroups.Matrix.Adjoint` — conjugation action, exp-conjugation compatibility
* `LieGroups.Measure.HaarAveraging` — Haar measure, invariant measures
* `LieGroups.Rep.Basic` — representations, invariants, equivariance
* `LieGroups.RootSystems.Bridge` — optional root systems / Weyl group bridge

## Usage

```lean
import HeytingLean.LieGroups
```

This gives you access to all the Lie group utilities.
-/
