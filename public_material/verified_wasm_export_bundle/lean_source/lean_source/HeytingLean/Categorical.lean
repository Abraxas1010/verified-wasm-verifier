import HeytingLean.Categorical.MonadAlgebra
import HeytingLean.Categorical.AlgebraHomomorphism
import HeytingLean.Categorical.KoopmanAlgebra
import HeytingLean.Categorical.TrainingStep

/-!
# HeytingLean Categorical Interface

This module provides the categorical interpretation of HeytingLean's
lattice-theoretic formalizations, connecting them to Categorical Deep
Learning (CDL).

## Overview

HeytingLean's nucleus operators ARE monad algebras, formalized in lattice
theory language. This module makes the correspondence explicit through
type aliases and documentation.

## Contents

- `MonadAlgebra`: Nucleus as monad algebra (T, η, μ)
- `AlgebraHomomorphism`: Nucleus-preserving maps as T-algebra morphisms
- `KoopmanAlgebra`: Koopman NBA as parametric coalgebra

## Existing CDL Infrastructure

The `HeytingLean.CDL` namespace contains extensive categorical formalization:
- `CDL.StrongMonad`: Strong monad class
- `CDL.Para`: Parametric category (1-cells, 2-cells, coherence)
- `CDL.LaxAlgebraComonoid`: Weight tying via comonoids

## Reference

Gavranovic et al., "Categorical Deep Learning is an Algebraic Theory of
All Architectures", ICML 2024, arXiv:2402.15332
-/
