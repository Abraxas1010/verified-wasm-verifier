/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

/-!
# HeytingVeil Packaging Core

Minimal CAB-style packaging hooks for carrying:
- specification identity,
- route metadata (IR/target path),
- proof/witness references,
- an explicit compliance proposition.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Packaging

/-- Minimal certificate payload for compiled-stage compliance claims. -/
structure CABCertificate where
  specId : String
  route : String
  proofRef : String
  witnessDigest : String
  witnessValid : Prop

/-- A certificate is compliant iff its witness proposition holds. -/
def compliant (cert : CABCertificate) : Prop :=
  cert.witnessValid

/-- Construct a certificate from route metadata and a witness proposition. -/
def mkCertificate (specId route proofRef witnessDigest : String)
    (witnessValid : Prop) : CABCertificate where
  specId := specId
  route := route
  proofRef := proofRef
  witnessDigest := witnessDigest
  witnessValid := witnessValid

theorem compliant_of_witness (specId route proofRef witnessDigest : String)
    (witnessValid : Prop) (h : witnessValid) :
    compliant (mkCertificate specId route proofRef witnessDigest witnessValid) := h

end Packaging
end HeytingVeil
end HeytingLean
