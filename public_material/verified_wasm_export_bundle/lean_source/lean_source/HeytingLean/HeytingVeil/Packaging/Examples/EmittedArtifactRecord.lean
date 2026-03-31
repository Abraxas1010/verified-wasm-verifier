/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Packaging.Examples.RouteTaggedCAB
import HeytingLean.HeytingVeil.Routing.DerivationHooks
import HeytingLean.LambdaIR.NatCompileFrag
import HeytingLean.LambdaIR.Nat2CompileFrag

/-!
# Emitted Artifact Records

Connect route-tagged CAB certificates to concrete backend artifacts derived
from MiniC compilation outputs.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Packaging
namespace Examples

open HeytingLean.HeytingVeil.Extract.Examples
open HeytingLean.HeytingVeil.Routing
open HeytingLean.LambdaIR.NatCompileFrag
open HeytingLean.LambdaIR.Nat2CompileFrag

structure EmittedArtifactRecord where
  cert : CABCertificate
  route : Route
  artifact : BackendArtifact
  route_consistent : cert.route = routeLabel route

def emitNatRecordWithPreference (B : NatFragmentBridge) (n : Nat)
    (preferredBackend? : Option BackendClass) : EmittedArtifactRecord :=
  let route := selectRoute IRClass.lambdaNat preferredBackend?
  let cert := routeTaggedNatCABWithPreference B n preferredBackend?
  let fn := compileNatFunFrag B.funName B.paramName B.t
  let artifact := deriveFromRoute route fn
  {
    cert := cert
    route := route
    artifact := artifact
    route_consistent := rfl
  }

def emitNatRecordHighIRC (B : NatFragmentBridge) (n : Nat) : EmittedArtifactRecord :=
  emitNatRecordWithPreference B n (some BackendClass.highIRC)

def emitNatRecord (B : NatFragmentBridge) (n : Nat) : EmittedArtifactRecord :=
  emitNatRecordWithPreference B n none

theorem emitNatRecordWithPreference_compliant (B : NatFragmentBridge) (n : Nat)
    (preferredBackend? : Option BackendClass) :
    compliant (emitNatRecordWithPreference B n preferredBackend?).cert := by
  exact routeTaggedNatCABWithPreference_compliant B n preferredBackend?

def emitNat2RecordWithPreference (B : Nat2FragmentBridge) (x y : Nat)
    (preferredBackend? : Option BackendClass) : EmittedArtifactRecord :=
  let route := selectRoute IRClass.lambdaNat2 preferredBackend?
  let cert := routeTaggedNat2CABWithPreference B x y preferredBackend?
  let fn := compileNat2FunFrag B.funName B.param1 B.param2 B.t
  let artifact := deriveFromRoute route fn
  {
    cert := cert
    route := route
    artifact := artifact
    route_consistent := rfl
  }

def emitNat2RecordHighIRC (B : Nat2FragmentBridge) (x y : Nat) : EmittedArtifactRecord :=
  emitNat2RecordWithPreference B x y (some BackendClass.highIRC)

def emitNat2Record (B : Nat2FragmentBridge) (x y : Nat) : EmittedArtifactRecord :=
  emitNat2RecordWithPreference B x y none

theorem emitNat2RecordWithPreference_compliant (B : Nat2FragmentBridge) (x y : Nat)
    (preferredBackend? : Option BackendClass) :
    compliant (emitNat2RecordWithPreference B x y preferredBackend?).cert := by
  exact routeTaggedNat2CABWithPreference_compliant B x y preferredBackend?

theorem emitNatRecord_compliant (B : NatFragmentBridge) (n : Nat) :
    compliant (emitNatRecord B n).cert := by
  exact routeTaggedNatCAB_compliant B n

theorem emitNat2Record_compliant (B : Nat2FragmentBridge) (x y : Nat) :
    compliant (emitNat2Record B x y).cert := by
  exact routeTaggedNat2CAB_compliant B x y

theorem emit_add1_record_compliant (n : Nat) :
    compliant (emitNatRecord add1Bridge n).cert :=
  emitNatRecord_compliant add1Bridge n

theorem emit_add2_record_compliant (x y : Nat) :
    compliant (emitNat2Record add2Bridge x y).cert :=
  emitNat2Record_compliant add2Bridge x y

end Examples
end Packaging
end HeytingVeil
end HeytingLean
