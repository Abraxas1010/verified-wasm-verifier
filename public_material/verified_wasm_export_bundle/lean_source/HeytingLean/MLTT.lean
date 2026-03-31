import HeytingLean.Certified.Basic
import HeytingLean.Certified.Subtype
import HeytingLean.Certified.Sigma
import HeytingLean.Erasure.Marker
import HeytingLean.Erasure.Fragment
import HeytingLean.LambdaIR.Certified
import HeytingLean.LambdaIR.Compile
import HeytingLean.Nucleus.Certified
import HeytingLean.Nucleus.Compile
import HeytingLean.Lens.Certified
import HeytingLean.Lens.Compile
import HeytingLean.CAB.Certified
import HeytingLean.CAB.Compile

/-!
# MLTT-style certified compilation infrastructure

This module groups the MLTT-inspired wrappers introduced in `WIP/mltt(1).md`:
certified values, erasure markers, fragment tags, and small integration shims for
LambdaIR, nuclei, lenses, and CAB artifacts.
-/
