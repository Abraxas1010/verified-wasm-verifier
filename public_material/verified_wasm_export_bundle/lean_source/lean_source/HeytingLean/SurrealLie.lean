/-
Copyright (c) 2026 Apoth3osis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.SurrealLie.Scale
import HeytingLean.SurrealLie.FormalLieGroup
import HeytingLean.SurrealLie.Flows
import HeytingLean.SurrealLie.KernelTrait
import HeytingLean.SurrealLie.FormalExpLog
import HeytingLean.SurrealLie.NilpotentExp
import HeytingLean.SurrealLie.NilpotentLog
import HeytingLean.SurrealLie.NilpotentMatrix
import HeytingLean.SurrealLie.Examples

/-!
# Surreal Lie Group Stack

This module re-exports the complete Surreal Lie stack for HeytingLean.

## Philosophy

In standard mathematics, infinitesimals in Lie theory are a figure of speech—
the Lie algebra is a "linear approximation" of the group. But over Surreal
numbers (or Hyperseries), the Lie algebra becomes an **exact microscope**
for infinitesimal structure.

## Contents

* `SurrealLie.Scale` — infinitesimal/infinite/macro predicates
* `SurrealLie.FormalLieGroup` — topology-free Lie group structure and flows
* `SurrealLie.Flows` — exp-connectedness and counterfactual stability
* `SurrealLie.KernelTrait` — agent-facing Lie action interface
* `SurrealLie.FormalExpLog` — truncated exp/log for nilpotent elements
* `SurrealLie.NilpotentExp` — Mathlib `IsNilpotent.exp` group-like laws
* `SurrealLie.NilpotentLog` — topology-free log skeleton for unipotent elements
* `SurrealLie.NilpotentMatrix` — nilpotent-matrix prototypes (topology-free exp/log)
* `SurrealLie.Examples` — scale examples and smoke tests

## Usage

```lean
import HeytingLean.SurrealLie
```

## Key Features

1. **Scale Predicates**: Formal definitions of infinitesimal/infinite/macro
   that work in any ordered field (especially non-Archimedean ones).

2. **Topology-Free Exp/Log**: Polynomial exp/log that are exact for nilpotent
   elements, requiring no analytic machinery.

3. **Formal flows and kernel hooks**: a topology-free `FormalLieGroup` plus
   counterfactual/flow utilities and a kernel-facing action trait.
-/
