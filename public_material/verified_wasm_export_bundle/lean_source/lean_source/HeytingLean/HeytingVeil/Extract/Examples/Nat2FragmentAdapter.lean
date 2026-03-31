/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Extract.Examples.LambdaNatBridge
import HeytingLean.LambdaIR.Add2EndToEnd
import HeytingLean.LambdaIR.Add2MiniCProof
import HeytingLean.LambdaIR.Nat2CompileFrag

/-!
# Nat2 Fragment Adapter

Nat->nat->nat counterpart to `NatFragmentAdapter`, parameterized by
`EndToEndNat2Spec` and instantiated with the existing add2 pipeline theorem.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Extract
namespace Examples

open HeytingLean.Core
open HeytingLean.LambdaIR
open HeytingLean.LambdaIR.Nat2CompileFrag
open HeytingLean.EndToEnd
open HeytingLean.HeytingVeil.Temporal
open HeytingLean.HeytingVeil.Verify
open HeytingLean.LambdaIR.Add2MiniCProof
open HeytingLean.LambdaIR.Add2EndToEnd

/-- Reusable bridge contract for nat->nat->nat compiler-correctness instances. -/
structure Nat2FragmentBridge where
  funName : String
  param1 : String
  param2 : String
  f : Nat → Nat → Nat
  t : Term [] (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat))
  e2e : EndToEndNat2Spec funName param1 param2 f t

namespace Nat2FragmentBridge

/-- Compiled observation at input pair `(x,y)`. -/
def compiledOut (B : Nat2FragmentBridge) (x y : Nat) : Option Nat :=
  runCompiledNat2FunFrag B.funName B.param1 B.param2 B.t x y

theorem compiledOut_spec (B : Nat2FragmentBridge) (x y : Nat) :
    B.compiledOut x y = some (B.f x y) :=
  B.e2e x y

/-- Program-indexed extraction bundle induced by a nat2-fragment bridge. -/
def bundle (B : Nat2FragmentBridge) (x y : Nat) :
    ExtractionBundle Unit (Option Nat) (Option Nat) where
  srcMachine := fun _ => observationMachine (some (B.f x y))
  tgtMachine := fun _ => observationMachine (B.compiledOut x y)
  encode := fun _ s => s
  simulation := by
    intro _
    refine ⟨?_, ?_⟩
    · intro s hs
      simpa [observationMachine] using hs
    · intro s t hstep
      have hOut : B.compiledOut x y = some (B.f x y) := B.compiledOut_spec x y
      simpa [observationMachine, hOut] using hstep

/-- Source safety transported from the target certificate. -/
theorem source_safety (B : Nat2FragmentBridge) (x y : Nat) :
    Safety ((B.bundle x y).sourceInv () (resolvedInv (B.compiledOut x y)))
      (resolvedTrace (some (B.f x y))) := by
  have hTargetCert :
      InvariantCert ((B.bundle x y).tgtMachine ()) (resolvedInv (B.compiledOut x y)) :=
    resolvedInv_cert (B.compiledOut x y)
  have hValid :
      ValidTrace ((B.bundle x y).srcMachine ()) (resolvedTrace (some (B.f x y))) := by
    simpa [bundle] using resolvedTrace_valid (some (B.f x y))
  exact (B.bundle x y).sourceSafetyOfTargetCert () hTargetCert hValid

end Nat2FragmentBridge

/-- add2 instance of the nat2 bridge. -/
def add2Bridge : Nat2FragmentBridge where
  funName := "add2"
  param1 := "x"
  param2 := "y"
  f := leanAdd2
  t := termAdd2IR
  e2e := add2_end_to_end

theorem add2_adapter_source_safety (x y : Nat) :
    Safety ((add2Bridge.bundle x y).sourceInv () (resolvedInv (add2Bridge.compiledOut x y)))
      (resolvedTrace (some (add2Bridge.f x y))) :=
  Nat2FragmentBridge.source_safety add2Bridge x y

end Examples
end Extract
end HeytingVeil
end HeytingLean
