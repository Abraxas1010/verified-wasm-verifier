/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Extract.Core
import HeytingLean.EndToEnd.NatFunSpec
import HeytingLean.LambdaIR.Add1EndToEnd
import HeytingLean.LambdaIR.Add1MiniCProof
import HeytingLean.LambdaIR.NatCompileFrag

/-!
# LambdaIR -> MiniC Bridge Example

Concrete Workstream-E bridge:
- reuse an existing LambdaIR-to-MiniC end-to-end theorem (`add1_end_to_end`),
- define source/target one-step machines over observation states,
- transport invariant certificates through the extraction/simulation API.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Extract
namespace Examples

open HeytingLean.HeytingVeil.Temporal
open HeytingLean.HeytingVeil.Verify
open HeytingLean.HeytingVeil.Propagate
open HeytingLean.EndToEnd
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.Add1MiniCProof
open HeytingLean.LambdaIR.Add1EndToEnd
open HeytingLean.LambdaIR.NatCompileFrag

/-- Single-observation machine: emit `out` at first step and then stutter. -/
def observationMachine (out : Option Nat) : Machine (Option Nat) where
  Init := fun s => s = none
  Step := fun s t => (s = none ∧ t = out) ∨ t = s

/-- Invariant for the observation machine: state is unresolved (`none`) or resolved (`out`). -/
def resolvedInv (out : Option Nat) : Option Nat → Prop :=
  fun s => s = none ∨ s = out

/-- `resolvedInv` is inductive for `observationMachine out`. -/
def resolvedInv_cert (out : Option Nat) :
    InvariantCert (observationMachine out) (resolvedInv out) where
  init_holds := by
    intro s hs
    exact Or.inl hs
  step_preserves := by
    intro s t hs hstep
    rcases hstep with hfirst | hstutter
    · exact Or.inr hfirst.2
    · rcases hs with hsnone | hsout
      · left
        simpa [hstutter] using hsnone
      · right
        simpa [hstutter] using hsout

/-- Canonical trace: unresolved at time `0`, then resolved forever. -/
def resolvedTrace (out : Option Nat) : Trace (Option Nat) :=
  fun n => if n = 0 then none else out

/-- Validity of the canonical trace for `observationMachine out`. -/
theorem resolvedTrace_valid (out : Option Nat) :
    ValidTrace (observationMachine out) (resolvedTrace out) := by
  constructor
  · simp [observationMachine, resolvedTrace]
  · intro n
    by_cases h0 : n = 0
    · subst h0
      simp [observationMachine, resolvedTrace]
    · have hsucc : n + 1 ≠ 0 := Nat.succ_ne_zero n
      right
      simp [resolvedTrace, h0]

/-- Compiled observation from the existing add1 LambdaIR -> MiniC pipeline. -/
def add1CompiledOut (n : Nat) : Option Nat :=
  runCompiledNatFunFrag "add1" "x" termAdd1IR n

theorem add1CompiledOut_spec (n : Nat) :
    add1CompiledOut n = some (leanAdd1 n) := by
  exact add1_end_to_end n

/-- Source/target extraction bundle for add1, instantiated at input `n`. -/
def add1BridgeBundle (n : Nat) : ExtractionBundle Unit (Option Nat) (Option Nat) where
  srcMachine := fun _ => observationMachine (some (leanAdd1 n))
  tgtMachine := fun _ => observationMachine (add1CompiledOut n)
  encode := fun _ s => s
  simulation := by
    intro _
    refine ⟨?_, ?_⟩
    · intro s hs
      simpa [observationMachine] using hs
    · intro s t hstep
      have hOut : add1CompiledOut n = some (leanAdd1 n) := add1CompiledOut_spec n
      simpa [observationMachine, hOut] using hstep

/-- Transported source safety witness over the add1 bridge. -/
theorem add1_bridge_source_safety (n : Nat) :
    Safety ((add1BridgeBundle n).sourceInv () (resolvedInv (add1CompiledOut n)))
      (resolvedTrace (some (leanAdd1 n))) := by
  have hTargetCert :
      InvariantCert ((add1BridgeBundle n).tgtMachine ()) (resolvedInv (add1CompiledOut n)) :=
    resolvedInv_cert (add1CompiledOut n)
  have hValid :
      ValidTrace ((add1BridgeBundle n).srcMachine ()) (resolvedTrace (some (leanAdd1 n))) := by
    simpa [add1BridgeBundle] using resolvedTrace_valid (some (leanAdd1 n))
  exact (add1BridgeBundle n).sourceSafetyOfTargetCert () hTargetCert hValid

end Examples
end Extract
end HeytingVeil
end HeytingLean
