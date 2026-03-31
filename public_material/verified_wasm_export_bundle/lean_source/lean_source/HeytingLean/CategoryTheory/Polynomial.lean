/-
Copyright (c) 2024 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Polynomial Functors
===================

This module provides a comprehensive library for polynomial functors,
ported from ToposInstitute/lean-poly.

## Contents

* `Basic` - Core definitions: Poly, polymap, category structure
* `Substitution` - Substitution product ◁, monoidal structure
* `Tensor` - Tensor product ⊗ᵖ, symmetric monoidal closed structure
* `Coproduct` - Coproduct +ᵖ, cartesian product ×ᵖ, or product ∨ᵖ

## Mathematical Background

A polynomial functor P is given by:
- `pos : Type` - the type of positions (shapes)
- `dir : pos → Type` - the type of directions at each position

This represents the functor `P(X) = Σ (p : pos), X^(dir p)`.

Morphisms between polynomial functors are called "lenses" and consist of:
- A forward map on positions
- A backward map on directions

## References

* [Polynomial Functors Book](https://toposinstitute.github.io/poly/poly-book.pdf)
* [nLab: Polynomial functor](https://ncatlab.org/nlab/show/polynomial+functor)
* [ToposInstitute/lean-poly](https://github.com/ToposInstitute/lean-poly)
* [sinhp/Poly](https://github.com/sinhp/Poly)
-/

import HeytingLean.CategoryTheory.Polynomial.Basic
import HeytingLean.CategoryTheory.Polynomial.Substitution
import HeytingLean.CategoryTheory.Polynomial.Tensor
import HeytingLean.CategoryTheory.Polynomial.Coproduct
import HeytingLean.CategoryTheory.Polynomial.ArchitectureGraph
