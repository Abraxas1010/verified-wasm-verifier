/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Extract.Examples.LambdaNatBridge
import HeytingLean.LambdaIR.DoubleEndToEnd
import HeytingLean.LambdaIR.DoubleMiniCProof
import HeytingLean.LambdaIR.Add1EndToEnd
import HeytingLean.LambdaIR.Add1MiniCProof

/-!
# Nat Fragment Adapter

Reusable adapter for nat->nat fragment theorems of shape `EndToEndNatSpec`.
This generalizes the concrete add1 bridge and demonstrates a second instance
(`double`) without changing extraction logic.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Extract
namespace Examples

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.NatCompileFrag
open HeytingLean.EndToEnd
open HeytingLean.HeytingVeil.Temporal
open HeytingLean.HeytingVeil.Verify
open HeytingLean.LambdaIR.Add1MiniCProof
open HeytingLean.LambdaIR.Add1EndToEnd
open HeytingLean.LambdaIR.DoubleMiniCProof
open HeytingLean.LambdaIR.DoubleEndToEnd

/-- Reusable bridge contract for nat->nat compiler-correctness instances. -/
structure NatFragmentBridge where
  funName : String
  paramName : String
  f : Nat → Nat
  t : Term [] (Ty.arrow Ty.nat Ty.nat)
  e2e : EndToEndNatSpec funName paramName f t

namespace NatFragmentBridge

/-- Compiled observation at input `n`. -/
def compiledOut (B : NatFragmentBridge) (n : Nat) : Option Nat :=
  runCompiledNatFunFrag B.funName B.paramName B.t n

theorem compiledOut_spec (B : NatFragmentBridge) (n : Nat) :
    B.compiledOut n = some (B.f n) :=
  B.e2e n

/-- Program-indexed extraction bundle induced by a nat-fragment bridge. -/
def bundle (B : NatFragmentBridge) (n : Nat) :
    ExtractionBundle Unit (Option Nat) (Option Nat) where
  srcMachine := fun _ => observationMachine (some (B.f n))
  tgtMachine := fun _ => observationMachine (B.compiledOut n)
  encode := fun _ s => s
  simulation := by
    intro _
    refine ⟨?_, ?_⟩
    · intro s hs
      simpa [observationMachine] using hs
    · intro s t hstep
      have hOut : B.compiledOut n = some (B.f n) := B.compiledOut_spec n
      simpa [observationMachine, hOut] using hstep

/-- Source safety transported from the target certificate. -/
theorem source_safety (B : NatFragmentBridge) (n : Nat) :
    Safety ((B.bundle n).sourceInv () (resolvedInv (B.compiledOut n)))
      (resolvedTrace (some (B.f n))) := by
  have hTargetCert :
      InvariantCert ((B.bundle n).tgtMachine ()) (resolvedInv (B.compiledOut n)) :=
    resolvedInv_cert (B.compiledOut n)
  have hValid :
      ValidTrace ((B.bundle n).srcMachine ()) (resolvedTrace (some (B.f n))) := by
    simpa [bundle] using resolvedTrace_valid (some (B.f n))
  exact (B.bundle n).sourceSafetyOfTargetCert () hTargetCert hValid

end NatFragmentBridge

/-- add1 instance of the reusable nat-fragment bridge. -/
def add1Bridge : NatFragmentBridge where
  funName := "add1"
  paramName := "x"
  f := leanAdd1
  t := termAdd1IR
  e2e := add1_end_to_end

/-- double instance of the reusable nat-fragment bridge. -/
def doubleBridge : NatFragmentBridge where
  funName := "double"
  paramName := "x"
  f := leanDouble
  t := termDoubleIR
  e2e := double_end_to_end

theorem add1_adapter_source_safety (n : Nat) :
    Safety ((add1Bridge.bundle n).sourceInv () (resolvedInv (add1Bridge.compiledOut n)))
      (resolvedTrace (some (add1Bridge.f n))) :=
  NatFragmentBridge.source_safety add1Bridge n

theorem double_adapter_source_safety (n : Nat) :
    Safety ((doubleBridge.bundle n).sourceInv () (resolvedInv (doubleBridge.compiledOut n)))
      (resolvedTrace (some (doubleBridge.f n))) :=
  NatFragmentBridge.source_safety doubleBridge n

end Examples
end Extract
end HeytingVeil
end HeytingLean
