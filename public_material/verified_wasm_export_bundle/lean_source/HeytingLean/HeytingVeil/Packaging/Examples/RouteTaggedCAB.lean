/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Packaging.Examples.NatBridgeCAB
import HeytingLean.HeytingVeil.Routing.Core

/-!
# Route-Tagged CAB Examples

Attach route-selection metadata from `HeytingVeil.Routing` to CAB certificates.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Packaging
namespace Examples

open HeytingLean.HeytingVeil.Extract.Examples
open HeytingLean.HeytingVeil.Routing

def routeTaggedNatCABWithPreference (B : NatFragmentBridge) (n : Nat)
    (preferredBackend? : Option BackendClass) : CABCertificate :=
  let r := selectRoute IRClass.lambdaNat preferredBackend?
  mkCertificate B.funName
    (routeLabel r)
    "EndToEndNatSpec"
    s!"{B.funName}:{n}:{routeLabel r}"
    (B.compiledOut n = some (B.f n))

def routeTaggedNatCAB (B : NatFragmentBridge) (n : Nat) : CABCertificate :=
  routeTaggedNatCABWithPreference B n none

theorem routeTaggedNatCABWithPreference_compliant (B : NatFragmentBridge) (n : Nat)
    (preferredBackend? : Option BackendClass) :
    compliant (routeTaggedNatCABWithPreference B n preferredBackend?) := by
  exact compliant_of_witness _ _ _ _ _ (B.compiledOut_spec n)

theorem routeTaggedNatCAB_compliant (B : NatFragmentBridge) (n : Nat) :
    compliant (routeTaggedNatCAB B n) := by
  simpa [routeTaggedNatCAB] using routeTaggedNatCABWithPreference_compliant B n none

def routeTaggedNat2CABWithPreference (B : Nat2FragmentBridge) (x y : Nat)
    (preferredBackend? : Option BackendClass) : CABCertificate :=
  let r := selectRoute IRClass.lambdaNat2 preferredBackend?
  mkCertificate B.funName
    (routeLabel r)
    "EndToEndNat2Spec"
    s!"{B.funName}:{x}:{y}:{routeLabel r}"
    (B.compiledOut x y = some (B.f x y))

def routeTaggedNat2CAB (B : Nat2FragmentBridge) (x y : Nat) : CABCertificate :=
  routeTaggedNat2CABWithPreference B x y none

theorem routeTaggedNat2CABWithPreference_compliant (B : Nat2FragmentBridge) (x y : Nat)
    (preferredBackend? : Option BackendClass) :
    compliant (routeTaggedNat2CABWithPreference B x y preferredBackend?) := by
  exact compliant_of_witness _ _ _ _ _ (B.compiledOut_spec x y)

theorem routeTaggedNat2CAB_compliant (B : Nat2FragmentBridge) (x y : Nat) :
    compliant (routeTaggedNat2CAB B x y) := by
  simpa [routeTaggedNat2CAB] using routeTaggedNat2CABWithPreference_compliant B x y none

theorem add1_routeTaggedCAB_compliant (n : Nat) :
    compliant (routeTaggedNatCAB add1Bridge n) :=
  routeTaggedNatCAB_compliant add1Bridge n

theorem add2_routeTaggedCAB_compliant (x y : Nat) :
    compliant (routeTaggedNat2CAB add2Bridge x y) :=
  routeTaggedNat2CAB_compliant add2Bridge x y

end Examples
end Packaging
end HeytingVeil
end HeytingLean
