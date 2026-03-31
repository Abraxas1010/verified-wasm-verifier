import Mathlib.Data.Set.Lattice
import HeytingLean.Constructor.CT.Core
import HeytingLean.Constructor.CT.Nucleus

/-
# CT Round-trip contracts (minimal scaffold)

This module provides a tiny round-trip style interface for CT task
families:
* `Encode` records an encoding of CT fixed-point task-sets into an
  arbitrary carrier `β`;
* `logicalShadow` collapses encoded CT theories back to their underlying
  sets of tasks.

Concrete substrates are expected to instantiate `Encode` for specific
carriers (graphs, tensor resources, quantum channels, …) and prove
stronger RT/triangulation properties there.
-/

namespace HeytingLean
namespace Contracts
namespace CT

open Constructor
open Constructor.CT

universe u v

variable {σ : Type u}

/-- CT encoding contract: packages an encoding of CT nucleus fixed-point
task-sets into an arbitrary carrier `β`, together with a left inverse
back to the CT fixed-point algebra.

This mirrors the shape of `Contracts.RoundTrip`, but specialised to the
`Ω_{J_CT}` fixed points rather than a LoF `Reentry`. -/
structure Encode (J : CTNucleus σ) (β : Type v) where
  /-- Encode a CT closed task-set as an element of `β`. -/
  encode : Omega J → β
  /-- Decode from `β` back into the CT fixed-point algebra. -/
  decode : β → Omega J
  /-- Round-trip: decoding after encoding returns the original CT
  closed task-set. -/
  round  : ∀ A, decode (encode A) = A

namespace Encode

variable {J : CTNucleus σ} (C : Encode (J := J) β)

/-- Logical shadow for CT: collapse an encoded element back to its
underlying set of tasks. -/
def logicalShadow (b : β) : Set (CT.Task σ) :=
  (C.decode b : Set (CT.Task σ))

@[simp] lemma logicalShadow_encode (A : Omega J) :
    logicalShadow (C := C) (C.encode A) = (A : Set (CT.Task σ)) := by
  unfold logicalShadow
  have h := C.round A
  simpa [h]

end Encode

end CT
end Contracts
end HeytingLean

