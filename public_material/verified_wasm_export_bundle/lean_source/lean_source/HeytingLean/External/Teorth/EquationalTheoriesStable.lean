/-
Teorth / Equational Theories (magmas) project.

Why this wrapper exists:
-- The upstream umbrella `equational_theories.lean` imports a very large module set, including
  files that still contain proof placeholders or tactics incompatible with our pinned toolchain.
- HeytingLean uses `--wfail` in its QA loop, so we need a curated subset that is proof-complete
  and warning-free under Lean v4.24.0 / Mathlib v4.24.0.

This wrapper intentionally excludes modules that still contain proof placeholders or rely on outdated
syntax (e.g., `Subgraph`, `ThreeC2`, some `ManuallyProved/*`), and focuses on the proof-complete
core: free magmas, equational laws, compactness/completeness, confluence, models, and related
infrastructure.
-/

import equational_theories.Magma
import equational_theories.MagmaLaw
import equational_theories.MagmaOp
import equational_theories.FreeMagma
import equational_theories.FreeComm
import equational_theories.Counting
import equational_theories.Equations.All
import equational_theories.Homomorphisms
import equational_theories.Compactness
import equational_theories.Completeness
import equational_theories.Definability.Basic
import equational_theories.Definability.Simple
import equational_theories.Definability.Law43
import equational_theories.Definability.Law46
import equational_theories.Definability.Tarski543
import equational_theories.FactsSyntax
import equational_theories.Preorder
import equational_theories.OrderMetatheorem
-- NOTE: InfModel / FiniteModel / LinearOps currently contain linter warnings or unfinished proofs
-- under Lean v4.24.0 and are intentionally excluded from the stable import set.
import equational_theories.Confluence1
import equational_theories.Confluence2
import equational_theories.Confluence3
import equational_theories.Confluence4
import equational_theories.WeakCentralGroupoids
import equational_theories.CentralGroupoids
import equational_theories.SmallMagmas
import equational_theories.StringMagmas
import equational_theories.Z3Counterexamples
import equational_theories.MemoFinOp
