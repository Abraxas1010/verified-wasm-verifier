/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Packaging.Core
import HeytingLean.HeytingVeil.Extract.Examples.NatFragmentAdapter
import HeytingLean.HeytingVeil.Extract.Examples.Nat2FragmentAdapter

/-!
# Nat Bridge CAB Examples

CAB-style certificates derived from compiled witness propositions emitted by
the reusable nat and nat2 bridge adapters.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Packaging
namespace Examples

open HeytingLean.HeytingVeil.Extract.Examples

def cabOfNatBridge (B : NatFragmentBridge) (n : Nat) : CABCertificate :=
  mkCertificate B.funName
    "LambdaIR->MiniC->C"
    "EndToEndNatSpec"
    s!"{B.funName}:{n}"
    (B.compiledOut n = some (B.f n))

theorem cabOfNatBridge_compliant (B : NatFragmentBridge) (n : Nat) :
    compliant (cabOfNatBridge B n) := by
  exact compliant_of_witness _ _ _ _ _ (B.compiledOut_spec n)

def cabOfNat2Bridge (B : Nat2FragmentBridge) (x y : Nat) : CABCertificate :=
  mkCertificate B.funName
    "LambdaIR2->MiniC->C"
    "EndToEndNat2Spec"
    s!"{B.funName}:{x}:{y}"
    (B.compiledOut x y = some (B.f x y))

theorem cabOfNat2Bridge_compliant (B : Nat2FragmentBridge) (x y : Nat) :
    compliant (cabOfNat2Bridge B x y) := by
  exact compliant_of_witness _ _ _ _ _ (B.compiledOut_spec x y)

/-- Concrete CAB compliance witness for the add1 bridge. -/
theorem add1_cab_compliant (n : Nat) :
    compliant (cabOfNatBridge add1Bridge n) :=
  cabOfNatBridge_compliant add1Bridge n

/-- Concrete CAB compliance witness for the add2 bridge. -/
theorem add2_cab_compliant (x y : Nat) :
    compliant (cabOfNat2Bridge add2Bridge x y) :=
  cabOfNat2Bridge_compliant add2Bridge x y

end Examples
end Packaging
end HeytingVeil
end HeytingLean
