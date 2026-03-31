/-
Copyright (c) 2024 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Fibred Category Theory
======================

This module provides the in-build fibred category theory surface, based on
LeanFibredCategories by Sina Hazratpour.

## Contents

Buildable core (strict, proof-escape-free):

* `Basic`: Fiber categories, based lifts, and their composition
* `CartesianLift`: Cartesian lift predicates, universal properties, composition
* `CoCartesianLift`: Cocartesian lift predicates, universal properties, composition
* `Fibration`: fibration/cloven fibration classes and transport surfaces
* `PolynomialBridge`: bridge surface between fibred and polynomial views

Still quarantined in `WIP/category_theory_fibred_port/` (contains proof holes or superseded
variants):

* `GrothendieckOpfibration.lean`
* `GrothendieckConstruction.lean` (superseded direction; see opfibration note)
* `CodFibration.lean`
* `DiscreteFibration.lean`

## References

* [LeanFibredCategories](https://github.com/sinhp/LeanFibredCategories) - Apache 2.0
* [nLab: Grothendieck fibration](https://ncatlab.org/nlab/show/Grothendieck+fibration)
* [nLab: Cartesian morphism](https://ncatlab.org/nlab/show/cartesian+morphism)
-/

import HeytingLean.CategoryTheory.Fibred.Basic
import HeytingLean.CategoryTheory.Fibred.CartesianLift
import HeytingLean.CategoryTheory.Fibred.CoCartesianLift
import HeytingLean.CategoryTheory.Fibred.Fibration
import HeytingLean.CategoryTheory.Fibred.PolynomialBridge
