/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Propagate.Core

/-!
# HeytingVeil Extract Core

Extraction interface from a program-level source machine to a target machine
that can be model-checked and verified.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Extract

open HeytingLean.HeytingVeil.Temporal
open HeytingLean.HeytingVeil.Verify
open HeytingLean.HeytingVeil.Propagate

universe u v w

/-- Program-indexed extraction bundle with a simulation witness. -/
structure ExtractionBundle (Prog : Type u) (SrcState : Type v) (TgtState : Type w) where
  srcMachine : Prog → Machine SrcState
  tgtMachine : Prog → Machine TgtState
  encode : (p : Prog) → SrcState → TgtState
  simulation : ∀ p : Prog, Simulation (srcMachine p) (tgtMachine p) (encode p)

namespace ExtractionBundle

variable {Prog : Type u} {SrcState : Type v} {TgtState : Type w}
variable (E : ExtractionBundle Prog SrcState TgtState)

/-- Source-level invariant induced from a target invariant through extraction map. -/
def sourceInv (p : Prog) (Inv : TgtState → Prop) : SrcState → Prop :=
  pullbackInv (E.encode p) Inv

/-- A target inductive certificate transports to a source inductive certificate. -/
def sourceCertOfTargetCert (p : Prog) {Inv : TgtState → Prop}
    (cert : InvariantCert (E.tgtMachine p) Inv) :
    InvariantCert (E.srcMachine p) (E.sourceInv p Inv) :=
  pullbackInvariantCert (sim := E.simulation p) cert

/-- Transported source certificate gives source-trace safety immediately. -/
theorem sourceSafetyOfTargetCert (p : Prog) {Inv : TgtState → Prop}
    (cert : InvariantCert (E.tgtMachine p) Inv)
    {σ : Trace SrcState} (hσ : ValidTrace (E.srcMachine p) σ) :
    Safety (E.sourceInv p Inv) σ :=
  safety_of_certificate (E.sourceCertOfTargetCert p cert) hσ

end ExtractionBundle

end Extract
end HeytingVeil
end HeytingLean
