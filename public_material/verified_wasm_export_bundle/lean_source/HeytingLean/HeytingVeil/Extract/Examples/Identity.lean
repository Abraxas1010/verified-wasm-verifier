/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Extract.Core
import HeytingLean.HeytingVeil.Verify.Examples.CounterexampleRefinement

/-!
# Identity Extraction Example

A minimal extraction witness where source and target machines coincide.
This checks the certificate-transport API end-to-end.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Extract
namespace Examples

open HeytingLean.HeytingVeil.Temporal
open HeytingLean.HeytingVeil.Verify
open HeytingLean.HeytingVeil.Verify.Examples
open HeytingLean.HeytingVeil.Propagate

/-- Trivial extraction bundle for the stabilization machine. -/
def idBundle : ExtractionBundle Unit Nat Nat where
  srcMachine := fun _ => stabilizeOneMachine
  tgtMachine := fun _ => stabilizeOneMachine
  encode := fun _ s => s
  simulation := by
    intro _
    refine ⟨?_, ?_⟩
    · intro s hs
      simpa using hs
    · intro s t hstep
      simpa using hstep

/-- Transporting the target certificate yields a source certificate. -/
def idBundle_source_inv1_cert :
    InvariantCert (idBundle.srcMachine ()) (idBundle.sourceInv () inv1) :=
  idBundle.sourceCertOfTargetCert () inv1_cert

/-- The transported certificate proves safety on the canonical valid trace. -/
theorem idBundle_source_inv1_safe_on_trace :
    Safety (idBundle.sourceInv () inv1) stabilizeOneTrace :=
  idBundle.sourceSafetyOfTargetCert () inv1_cert stabilizeOneTrace_valid

end Examples
end Extract
end HeytingVeil
end HeytingLean
